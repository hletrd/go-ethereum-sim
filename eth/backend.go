// Copyright 2014 The go-ethereum Authors
// This file is part of the go-ethereum library.
//
// The go-ethereum library is free software: you can redistribute it and/or modify
// it under the terms of the GNU Lesser General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.
//
// The go-ethereum library is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
// GNU Lesser General Public License for more details.
//
// You should have received a copy of the GNU Lesser General Public License
// along with the go-ethereum library. If not, see <http://www.gnu.org/licenses/>.

// Package eth implements the Ethereum protocol.
package eth

/*
#include <pthread.h>
#include <time.h>
#include <stdio.h>

static unsigned long long getCPUTimeNs() {
	struct timespec t;
	if (clock_gettime(CLOCK_PROCESS_CPUTIME_ID, &t)) {
		perror("clock_gettime");
		return 0;
	}
	//Probably cause some trouble if POSIX epoch passes n * 1000000000
	return t.tv_sec * 1000000000ULL + t.tv_nsec;
}
*/
import "C"

import (
	"database/sql"
	"encoding/binary"
	"errors"
	"fmt"
	"math/big"
	"runtime"
	"strings"
	"sync"
	"sync/atomic"

	_ "github.com/go-sql-driver/mysql"

	"github.com/ethereum/go-ethereum/accounts"
	"github.com/ethereum/go-ethereum/common"
	"github.com/ethereum/go-ethereum/common/hexutil"
	"github.com/ethereum/go-ethereum/consensus"
	"github.com/ethereum/go-ethereum/consensus/beacon"
	"github.com/ethereum/go-ethereum/consensus/clique"
	"github.com/ethereum/go-ethereum/consensus/ethash"
	"github.com/ethereum/go-ethereum/core"
	"github.com/ethereum/go-ethereum/core/bloombits"
	"github.com/ethereum/go-ethereum/core/rawdb"
	"github.com/ethereum/go-ethereum/core/state/pruner"
	"github.com/ethereum/go-ethereum/core/types"
	"github.com/ethereum/go-ethereum/core/vm"
	"github.com/ethereum/go-ethereum/eth/downloader"
	"github.com/ethereum/go-ethereum/eth/ethconfig"
	"github.com/ethereum/go-ethereum/eth/gasprice"
	"github.com/ethereum/go-ethereum/eth/protocols/eth"
	"github.com/ethereum/go-ethereum/eth/protocols/snap"
	"github.com/ethereum/go-ethereum/ethdb"
	"github.com/ethereum/go-ethereum/event"
	"github.com/ethereum/go-ethereum/internal/ethapi"
	"github.com/ethereum/go-ethereum/internal/shutdowncheck"
	"github.com/ethereum/go-ethereum/log"
	"github.com/ethereum/go-ethereum/miner"
	"github.com/ethereum/go-ethereum/node"
	"github.com/ethereum/go-ethereum/p2p"
	"github.com/ethereum/go-ethereum/p2p/dnsdisc"
	"github.com/ethereum/go-ethereum/p2p/enode"
	"github.com/ethereum/go-ethereum/params"
	"github.com/ethereum/go-ethereum/rlp"
	"github.com/ethereum/go-ethereum/rpc"
)

// errors for DB handler (hletrd)
var (
	ErrFetchBlock = errors.New("Failed to fetch a block")
	ErrFetchTxs = errors.New("Failed to fetch txs")
	ErrFetchUncles = errors.New("Failed to fetch uncles")
)

// Config contains the configuration options of the ETH protocol.
// Deprecated: use ethconfig.Config instead.
type Config = ethconfig.Config

// Ethereum implements the Ethereum full node service.
type Ethereum struct {
	config *ethconfig.Config

	// Handlers
	txPool             *core.TxPool
	blockchain         *core.BlockChain
	handler            *handler
	ethDialCandidates  enode.Iterator
	snapDialCandidates enode.Iterator
	merger             *consensus.Merger

	// DB interfaces
	chainDb ethdb.Database // Block chain database

	eventMux       *event.TypeMux
	engine         consensus.Engine
	accountManager *accounts.Manager

	bloomRequests     chan chan *bloombits.Retrieval // Channel receiving bloom data retrieval requests
	bloomIndexer      *core.ChainIndexer             // Bloom indexer operating during block imports
	closeBloomHandler chan struct{}

	APIBackend *EthAPIBackend

	miner     *miner.Miner
	gasPrice  *big.Int
	etherbase common.Address

	networkID     uint64
	netRPCService *ethapi.NetAPI

	p2pServer *p2p.Server

	lock sync.RWMutex // Protects the variadic fields (e.g. gas price and etherbase)

	shutdownTracker *shutdowncheck.ShutdownTracker // Tracks if and when the node has shutdown ungracefully

	sql *sql.DB

	timer_cpu_insert uint64
	timer_cpu_db uint64
	timer_cpu_db_block uint64
	timer_cpu_db_tx uint64
	timer_cpu_db_accesslist uint64
	timer_cpu_db_uncle uint64

	timer_insert uint64
	timer_db uint64
	timer_db_block uint64
	timer_db_tx uint64
	timer_db_accesslist uint64
	timer_db_uncle uint64
}

// New creates a new Ethereum object (including the
// initialisation of the common Ethereum object)
func New(stack *node.Node, config *ethconfig.Config) (*Ethereum, error) {
	// Ensure configuration values are compatible and sane
	if config.SyncMode == downloader.LightSync {
		return nil, errors.New("can't run eth.Ethereum in light sync mode, use les.LightEthereum")
	}
	if !config.SyncMode.IsValid() {
		return nil, fmt.Errorf("invalid sync mode %d", config.SyncMode)
	}
	if config.Miner.GasPrice == nil || config.Miner.GasPrice.Cmp(common.Big0) <= 0 {
		log.Warn("Sanitizing invalid miner gas price", "provided", config.Miner.GasPrice, "updated", ethconfig.Defaults.Miner.GasPrice)
		config.Miner.GasPrice = new(big.Int).Set(ethconfig.Defaults.Miner.GasPrice)
	}
	if config.NoPruning && config.TrieDirtyCache > 0 {
		if config.SnapshotCache > 0 {
			config.TrieCleanCache += config.TrieDirtyCache * 3 / 5
			config.SnapshotCache += config.TrieDirtyCache * 2 / 5
		} else {
			config.TrieCleanCache += config.TrieDirtyCache
		}
		config.TrieDirtyCache = 0
	}
	log.Info("Allocated trie memory caches", "clean", common.StorageSize(config.TrieCleanCache)*1024*1024, "dirty", common.StorageSize(config.TrieDirtyCache)*1024*1024)

	// Transfer mining-related config to the ethash config.
	ethashConfig := config.Ethash
	ethashConfig.NotifyFull = config.Miner.NotifyFull

	// Assemble the Ethereum object
	chainDb, err := stack.OpenDatabaseWithFreezer("chaindata", config.DatabaseCache, config.DatabaseHandles, config.DatabaseFreezer, "eth/db/chaindata/", false)
	if err != nil {
		return nil, err
	}
	chainConfig, genesisHash, genesisErr := core.SetupGenesisBlockWithOverride(chainDb, config.Genesis, config.OverrideTerminalTotalDifficulty, config.OverrideTerminalTotalDifficultyPassed)
	if _, ok := genesisErr.(*params.ConfigCompatError); genesisErr != nil && !ok {
		return nil, genesisErr
	}
	log.Info("")
	log.Info(strings.Repeat("-", 153))
	for _, line := range strings.Split(chainConfig.String(), "\n") {
		log.Info(line)
	}
	log.Info(strings.Repeat("-", 153))
	log.Info("")

	if err := pruner.RecoverPruning(stack.ResolvePath(""), chainDb, stack.ResolvePath(config.TrieCleanCacheJournal)); err != nil {
		log.Error("Failed to recover state", "error", err)
	}
	merger := consensus.NewMerger(chainDb)
	eth := &Ethereum{
		config:            config,
		merger:            merger,
		chainDb:           chainDb,
		eventMux:          stack.EventMux(),
		accountManager:    stack.AccountManager(),
		engine:            ethconfig.CreateConsensusEngine(stack, chainConfig, &ethashConfig, config.Miner.Notify, config.Miner.Noverify, chainDb),
		closeBloomHandler: make(chan struct{}),
		networkID:         config.NetworkId,
		gasPrice:          config.Miner.GasPrice,
		etherbase:         config.Miner.Etherbase,
		bloomRequests:     make(chan chan *bloombits.Retrieval),
		bloomIndexer:      core.NewBloomIndexer(chainDb, params.BloomBitsBlocks, params.BloomConfirms),
		p2pServer:         stack.Server(),
		shutdownTracker:   shutdowncheck.NewShutdownTracker(chainDb),
	}

	bcVersion := rawdb.ReadDatabaseVersion(chainDb)
	var dbVer = "<nil>"
	if bcVersion != nil {
		dbVer = fmt.Sprintf("%d", *bcVersion)
	}
	log.Info("Initialising Ethereum protocol", "network", config.NetworkId, "dbversion", dbVer)

	if !config.SkipBcVersionCheck {
		if bcVersion != nil && *bcVersion > core.BlockChainVersion {
			return nil, fmt.Errorf("database version is v%d, Geth %s only supports v%d", *bcVersion, params.VersionWithMeta, core.BlockChainVersion)
		} else if bcVersion == nil || *bcVersion < core.BlockChainVersion {
			if bcVersion != nil { // only print warning on upgrade, not on init
				log.Warn("Upgrade blockchain database version", "from", dbVer, "to", core.BlockChainVersion)
			}
			rawdb.WriteDatabaseVersion(chainDb, core.BlockChainVersion)
		}
	}
	var (
		vmConfig = vm.Config{
			EnablePreimageRecording: config.EnablePreimageRecording,
		}
		cacheConfig = &core.CacheConfig{
			TrieCleanLimit:      config.TrieCleanCache,
			TrieCleanJournal:    stack.ResolvePath(config.TrieCleanCacheJournal),
			TrieCleanRejournal:  config.TrieCleanCacheRejournal,
			TrieCleanNoPrefetch: config.NoPrefetch,
			TrieDirtyLimit:      config.TrieDirtyCache,
			TrieDirtyDisabled:   config.NoPruning,
			TrieTimeLimit:       config.TrieTimeout,
			SnapshotLimit:       config.SnapshotCache,
			Preimages:           config.Preimages,
		}
	)
	eth.blockchain, err = core.NewBlockChain(chainDb, cacheConfig, chainConfig, eth.engine, vmConfig, eth.shouldPreserve, &config.TxLookupLimit)
	if err != nil {
		return nil, err
	}
	// Rewind the chain in case of an incompatible config upgrade.
	if compat, ok := genesisErr.(*params.ConfigCompatError); ok {
		log.Warn("Rewinding chain to upgrade configuration", "err", compat)
		eth.blockchain.SetHead(compat.RewindTo)
		rawdb.WriteChainConfig(chainDb, genesisHash, chainConfig)
	}
	eth.bloomIndexer.Start(eth.blockchain)

	if config.TxPool.Journal != "" {
		config.TxPool.Journal = stack.ResolvePath(config.TxPool.Journal)
	}
	eth.txPool = core.NewTxPool(config.TxPool, chainConfig, eth.blockchain)

	// Permit the downloader to use the trie cache allowance during fast sync
	cacheLimit := cacheConfig.TrieCleanLimit + cacheConfig.TrieDirtyLimit + cacheConfig.SnapshotLimit
	checkpoint := config.Checkpoint
	if checkpoint == nil {
		checkpoint = params.TrustedCheckpoints[genesisHash]
	}
	if eth.handler, err = newHandler(&handlerConfig{
		Database:       chainDb,
		Chain:          eth.blockchain,
		TxPool:         eth.txPool,
		Merger:         merger,
		Network:        config.NetworkId,
		Sync:           config.SyncMode,
		BloomCache:     uint64(cacheLimit),
		EventMux:       eth.eventMux,
		Checkpoint:     checkpoint,
		RequiredBlocks: config.RequiredBlocks,
	}); err != nil {
		return nil, err
	}

	eth.miner = miner.New(eth, &config.Miner, chainConfig, eth.EventMux(), eth.engine, eth.isLocalBlock)
	eth.miner.SetExtra(makeExtraData(config.Miner.ExtraData))

	eth.APIBackend = &EthAPIBackend{stack.Config().ExtRPCEnabled(), stack.Config().AllowUnprotectedTxs, eth, nil}
	if eth.APIBackend.allowUnprotectedTxs {
		log.Info("Unprotected transactions allowed")
	}
	gpoParams := config.GPO
	if gpoParams.Default == nil {
		gpoParams.Default = config.Miner.GasPrice
	}
	eth.APIBackend.gpo = gasprice.NewOracle(eth.APIBackend, gpoParams)

	// Setup DNS discovery iterators.
	dnsclient := dnsdisc.NewClient(dnsdisc.Config{})
	eth.ethDialCandidates, err = dnsclient.NewIterator(eth.config.EthDiscoveryURLs...)
	if err != nil {
		return nil, err
	}
	eth.snapDialCandidates, err = dnsclient.NewIterator(eth.config.SnapDiscoveryURLs...)
	if err != nil {
		return nil, err
	}

	// Start the RPC service
	eth.netRPCService = ethapi.NewNetAPI(eth.p2pServer, config.NetworkId)

	// Register the backend on the node
	stack.RegisterAPIs(eth.APIs())
	stack.RegisterProtocols(eth.Protocols())
	stack.RegisterLifecycle(eth)

	// Successful startup; push a marker and check previous unclean shutdowns.
	eth.shutdownTracker.MarkStartup()

	return eth, nil
}

func makeExtraData(extra []byte) []byte {
	if len(extra) == 0 {
		// create default extradata
		extra, _ = rlp.EncodeToBytes([]interface{}{
			uint(params.VersionMajor<<16 | params.VersionMinor<<8 | params.VersionPatch),
			"geth",
			runtime.Version(),
			runtime.GOOS,
		})
	}
	if uint64(len(extra)) > params.MaximumExtraDataSize {
		log.Warn("Miner extra data exceed limit", "extra", hexutil.Bytes(extra), "limit", params.MaximumExtraDataSize)
		extra = nil
	}
	return extra
}

// APIs return the collection of RPC services the ethereum package offers.
// NOTE, some of these services probably need to be moved to somewhere else.
func (s *Ethereum) APIs() []rpc.API {
	apis := ethapi.GetAPIs(s.APIBackend)

	// Append any APIs exposed explicitly by the consensus engine
	apis = append(apis, s.engine.APIs(s.BlockChain())...)

	// Append all the local APIs and return
	return append(apis, []rpc.API{
		{
			Namespace: "eth",
			Service:   NewEthereumAPI(s),
		}, {
			Namespace: "miner",
			Service:   NewMinerAPI(s),
		}, {
			Namespace: "eth",
			Service:   downloader.NewDownloaderAPI(s.handler.downloader, s.eventMux),
		}, {
			Namespace: "admin",
			Service:   NewAdminAPI(s),
		}, {
			Namespace: "debug",
			Service:   NewDebugAPI(s),
		}, {
			Namespace: "net",
			Service:   s.netRPCService,
		},
	}...)
}

func (s *Ethereum) ResetWithGenesisBlock(gb *types.Block) {
	s.blockchain.ResetWithGenesisBlock(gb)
}

func (s *Ethereum) Etherbase() (eb common.Address, err error) {
	s.lock.RLock()
	etherbase := s.etherbase
	s.lock.RUnlock()

	if etherbase != (common.Address{}) {
		return etherbase, nil
	}
	if wallets := s.AccountManager().Wallets(); len(wallets) > 0 {
		if accounts := wallets[0].Accounts(); len(accounts) > 0 {
			etherbase := accounts[0].Address

			s.lock.Lock()
			s.etherbase = etherbase
			s.lock.Unlock()

			log.Info("Etherbase automatically configured", "address", etherbase)
			return etherbase, nil
		}
	}
	return common.Address{}, fmt.Errorf("etherbase must be explicitly specified")
}

// isLocalBlock checks whether the specified block is mined
// by local miner accounts.
//
// We regard two types of accounts as local miner account: etherbase
// and accounts specified via `txpool.locals` flag.
func (s *Ethereum) isLocalBlock(header *types.Header) bool {
	author, err := s.engine.Author(header)
	if err != nil {
		log.Warn("Failed to retrieve block author", "number", header.Number.Uint64(), "hash", header.Hash(), "err", err)
		return false
	}
	// Check whether the given address is etherbase.
	s.lock.RLock()
	etherbase := s.etherbase
	s.lock.RUnlock()
	if author == etherbase {
		return true
	}
	// Check whether the given address is specified by `txpool.local`
	// CLI flag.
	for _, account := range s.config.TxPool.Locals {
		if account == author {
			return true
		}
	}
	return false
}

// shouldPreserve checks whether we should preserve the given block
// during the chain reorg depending on whether the author of block
// is a local account.
func (s *Ethereum) shouldPreserve(header *types.Header) bool {
	// The reason we need to disable the self-reorg preserving for clique
	// is it can be probable to introduce a deadlock.
	//
	// e.g. If there are 7 available signers
	//
	// r1   A
	// r2     B
	// r3       C
	// r4         D
	// r5   A      [X] F G
	// r6    [X]
	//
	// In the round5, the inturn signer E is offline, so the worst case
	// is A, F and G sign the block of round5 and reject the block of opponents
	// and in the round6, the last available signer B is offline, the whole
	// network is stuck.
	if _, ok := s.engine.(*clique.Clique); ok {
		return false
	}
	return s.isLocalBlock(header)
}

// SetEtherbase sets the mining reward address.
func (s *Ethereum) SetEtherbase(etherbase common.Address) {
	s.lock.Lock()
	s.etherbase = etherbase
	s.lock.Unlock()

	s.miner.SetEtherbase(etherbase)
}

// StartMining starts the miner with the given number of CPU threads. If mining
// is already running, this method adjust the number of threads allowed to use
// and updates the minimum price required by the transaction pool.
func (s *Ethereum) StartMining(threads int) error {
	// Update the thread count within the consensus engine
	type threaded interface {
		SetThreads(threads int)
	}
	if th, ok := s.engine.(threaded); ok {
		log.Info("Updated mining threads", "threads", threads)
		if threads == 0 {
			threads = -1 // Disable the miner from within
		}
		th.SetThreads(threads)
	}
	// If the miner was not running, initialize it
	if !s.IsMining() {
		// Propagate the initial price point to the transaction pool
		s.lock.RLock()
		price := s.gasPrice
		s.lock.RUnlock()
		s.txPool.SetGasPrice(price)

		// Configure the local mining address
		eb, err := s.Etherbase()
		if err != nil {
			log.Error("Cannot start mining without etherbase", "err", err)
			return fmt.Errorf("etherbase missing: %v", err)
		}
		var cli *clique.Clique
		if c, ok := s.engine.(*clique.Clique); ok {
			cli = c
		} else if cl, ok := s.engine.(*beacon.Beacon); ok {
			if c, ok := cl.InnerEngine().(*clique.Clique); ok {
				cli = c
			}
		}
		if cli != nil {
			wallet, err := s.accountManager.Find(accounts.Account{Address: eb})
			if wallet == nil || err != nil {
				log.Error("Etherbase account unavailable locally", "err", err)
				return fmt.Errorf("signer missing: %v", err)
			}
			cli.Authorize(eb, wallet.SignData)
		}
		// If mining is started, we can disable the transaction rejection mechanism
		// introduced to speed sync times.
		atomic.StoreUint32(&s.handler.acceptTxs, 1)

		// (hletrd)
		go s.miner.Start(eb)
	}
	return nil
}

// StopMining terminates the miner, both at the consensus engine level as well as
// at the block creation level.
func (s *Ethereum) StopMining() {
	// Update the thread count within the consensus engine
	type threaded interface {
		SetThreads(threads int)
	}
	if th, ok := s.engine.(threaded); ok {
		th.SetThreads(-1)
	}
	// Stop the block creating itself
	s.miner.Stop()
}

func (s *Ethereum) IsMining() bool      { return s.miner.Mining() }
func (s *Ethereum) Miner() *miner.Miner { return s.miner }

func (s *Ethereum) AccountManager() *accounts.Manager  { return s.accountManager }
func (s *Ethereum) BlockChain() *core.BlockChain       { return s.blockchain }
func (s *Ethereum) TxPool() *core.TxPool               { return s.txPool }
func (s *Ethereum) EventMux() *event.TypeMux           { return s.eventMux }
func (s *Ethereum) Engine() consensus.Engine           { return s.engine }
func (s *Ethereum) ChainDb() ethdb.Database            { return s.chainDb }
func (s *Ethereum) IsListening() bool                  { return true } // Always listening
func (s *Ethereum) Downloader() *downloader.Downloader { return s.handler.downloader }
func (s *Ethereum) Synced() bool                       { return atomic.LoadUint32(&s.handler.acceptTxs) == 1 }
func (s *Ethereum) SetSynced()                         { atomic.StoreUint32(&s.handler.acceptTxs, 1) }
func (s *Ethereum) ArchiveMode() bool                  { return s.config.NoPruning }
func (s *Ethereum) BloomIndexer() *core.ChainIndexer   { return s.bloomIndexer }
func (s *Ethereum) Merger() *consensus.Merger          { return s.merger }
func (s *Ethereum) SyncMode() downloader.SyncMode {
	mode, _ := s.handler.chainSync.modeAndLocalHead()
	return mode
}

// Protocols returns all the currently configured
// network protocols to start.
func (s *Ethereum) Protocols() []p2p.Protocol {
	protos := eth.MakeProtocols((*ethHandler)(s.handler), s.networkID, s.ethDialCandidates)
	if s.config.SnapshotCache > 0 {
		protos = append(protos, snap.MakeProtocols((*snapHandler)(s.handler), s.snapDialCandidates)...)
	}
	return protos
}

// Start implements node.Lifecycle, starting all internal goroutines needed by the
// Ethereum protocol implementation.
func (s *Ethereum) Start() error {
	eth.StartENRUpdater(s.blockchain, s.p2pServer.LocalNode())

	// Start the bloom bits servicing goroutines
	s.startBloomHandlers(params.BloomBitsBlocks)

	// Regularly update shutdown marker
	s.shutdownTracker.Start()

	// Figure out a max peers count based on the server limits
	maxPeers := s.p2pServer.MaxPeers
	if s.config.LightServ > 0 {
		if s.config.LightPeers >= s.p2pServer.MaxPeers {
			return fmt.Errorf("invalid peer config: light peer count (%d) >= total peer count (%d)", s.config.LightPeers, s.p2pServer.MaxPeers)
		}
		maxPeers -= s.config.LightPeers
	}
	// Start the networking layer and the light server if requested
	s.handler.Start(maxPeers)
	return nil
}

// Stop implements node.Lifecycle, terminating all internal goroutines used by the
// Ethereum protocol.
func (s *Ethereum) Stop() error {
	// Stop all the peer-related stuff first.
	s.ethDialCandidates.Close()
	s.snapDialCandidates.Close()
	s.handler.Stop()

	// Then stop everything else.
	s.bloomIndexer.Close()
	close(s.closeBloomHandler)
	s.txPool.Stop()
	s.miner.Close()
	s.blockchain.Stop()
	s.engine.Close()

	// Clean shutdown marker as the last thing before closing db
	s.shutdownTracker.Stop()

	s.chainDb.Close()
	s.eventMux.Stop()

	return nil
}

// Connect to an SQL server (hletrd)
func (s *Ethereum) connectSQL(username string, password string) bool {
	var err error
	s.sql, err = sql.Open("mysql", username + ":" + password + "@/ethereum")
	if err != nil {
		log.Error("[backend.go/connectSQL] connection failed")
		return false
	}

	s.timer_cpu_insert = 0
	s.timer_cpu_db = 0
	s.timer_cpu_db_block = 0
	s.timer_cpu_db_tx = 0
	s.timer_cpu_db_accesslist = 0
	s.timer_cpu_db_uncle = 0

	s.timer_insert = 0
	s.timer_db = 0
	s.timer_db_block = 0
	s.timer_db_tx = 0
	s.timer_db_accesslist = 0
	s.timer_db_uncle = 0

	return true
}

// read blocks as a batch (hletrd)
func (s *Ethereum) readBlockBatch(start int, end int) ([]*types.Header, error) {
	timer_cpu_db_start := C.getCPUTimeNs()

	block_db, err := s.sql.Query("SELECT `number`, `timestamp`, `miner`, `difficulty`, `gaslimit`, `extradata`, `nonce`, `mixhash`, `basefee` FROM `blocks` WHERE `number` >= ? AND `number` < ?", start, end)
	if err != nil {
		log.Error("[backend.go/readBlockBatch] failed to read blocks", "start", start, "end", end)
		return nil, ErrFetchTxs
	}
	defer block_db.Close()

	var blocknumber_i uint64; var blocknumber *big.Int
	var timestamp uint64
	var miner_b []byte; var miner common.Address
	var difficulty_i uint64; var difficulty *big.Int
	var gaslimit uint64
	var extradata []byte
	var nonce_b []byte; var nonce types.BlockNonce
	var mixhash_b []byte; var mixhash common.Hash
	var basefee sql.NullInt64

	result := make([]*types.Header, end - start)
	seq := 0

	for block_db.Next() {
		err := block_db.Scan(&blocknumber_i, &timestamp, &miner_b, &difficulty_i, &gaslimit, &extradata, &nonce_b, &mixhash_b, &basefee)

		_ = mixhash

		if err != nil {
			log.Error("[backend.go/readBlockBatch] failed to read a block", "number", blocknumber_i, "err", err);
			return nil, ErrFetchBlock
		}

		miner = common.BytesToAddress(miner_b)
		difficulty = new(big.Int).SetUint64(difficulty_i)
		blocknumber = new(big.Int).SetUint64(blocknumber_i)
		mixhash = common.BytesToHash(mixhash_b)
		nonce = types.EncodeNonce(binary.BigEndian.Uint64(nonce_b))

		header := &types.Header{
			Coinbase: miner,
			Difficulty: difficulty,
			Number: blocknumber,
			GasLimit: gaslimit,
			Time: timestamp,
			Extra: extradata,
			MixDigest: mixhash,
			Nonce: nonce,
			BaseFee: nil,
		}

		if basefee.Valid {
			header.BaseFee = new(big.Int).SetUint64(uint64(basefee.Int64))
		}
		result[seq] = header
		seq++
	}

	timer_cpu_db_end := C.getCPUTimeNs()
	cputime := (uint64(timer_cpu_db_end) - uint64(timer_cpu_db_start))
	s.timer_cpu_db += cputime
	s.timer_cpu_db_block += cputime

	return result, nil
}

// read txs as a batch (hletrd)
func (s *Ethereum) readTransactionsBatch(start int, end int) ([][]*types.Transaction, error) {
	timer_cpu_db_start := C.getCPUTimeNs()

	tx_db, err := s.sql.Query("SELECT `blocknumber`, `to`, `gas`, `gasprice`, `input`, `nonce`, `value`, `v`, `r`, `s`, `type`, `maxfeepergas`, `maxpriorityfeepergas` FROM `transactions` WHERE `blocknumber` >= ? AND `blocknumber` < ?", start, end)
	if err != nil {
		log.Error("[backend.go/readTransactionsBatch] failed to read txs", "start", start, "end", end)
		return nil, ErrFetchTxs
	}
	defer tx_db.Close()

	blocknumber_i := uint64(start)
	var to_b sql.NullString; var to *common.Address
	var gas uint64
	var gasprice_i uint64
	var gasprice *big.Int
	var input []byte
	var nonce uint64
	var value_b []byte; var value *big.Int
	var V_b []byte; var V *big.Int
	var R_b []byte; var R *big.Int
	var S_b []byte; var S *big.Int
	var type_b []byte; var type_ byte
	var maxfeepergas sql.NullInt64; var maxpriorityfeepergas sql.NullInt64

	result := make([][]*types.Transaction, end - start)
	var txs []*types.Transaction
	seq := uint64(start)

	for tx_db.Next() {
		if err := tx_db.Scan(&blocknumber_i, &to_b, &gas, &gasprice_i, &input, &nonce, &value_b, &V_b, &R_b, &S_b, &type_b, &maxfeepergas, &maxpriorityfeepergas); err != nil {
			log.Error("[backend.go/readTransactionsBatch] failed to read a tx from block", "block", blocknumber_i)
			return nil, ErrFetchTxs
		}
		_ = type_

		if to_b.Valid {
			to_addr := common.BytesToAddress([]byte(to_b.String))
			to = &to_addr
		} else {
			to = nil
		}

		gasprice = new(big.Int).SetUint64(gasprice_i)
		value, _ = new(big.Int).SetString(string(value_b[:]), 10)
		V = new(big.Int).SetBytes(V_b)
		R = new(big.Int).SetBytes(R_b)
		S = new(big.Int).SetBytes(S_b)
		type_ = type_b[0]

		var txdata types.TxData

		switch type_ {
		case types.LegacyTxType:
			txdata = &types.LegacyTx{
				Nonce: nonce,
				GasPrice: gasprice,
				Gas: gas,
				To: to,
				Value: value,
				Data: input,
				V: V,
				R: R,
				S: S,
			}
		case types.AccessListTxType:
			txdata = &types.AccessListTx{
				ChainID: s.blockchain.Config().ChainID,
				Nonce: nonce,
				GasPrice: gasprice,
				Gas: gas,
				To: to,
				Value: value,
				Data: input,
				V: V,
				R: R,
				S: S,
			}		
		case types.DynamicFeeTxType:
			txdata = &types.DynamicFeeTx{
				ChainID: s.blockchain.Config().ChainID,
				Nonce: nonce,
				Gas: gas,
				GasTipCap: new(big.Int).SetInt64(maxfeepergas.Int64),
				GasFeeCap: new(big.Int).SetInt64(maxpriorityfeepergas.Int64),
				To: to,
				Value: value,
				Data: input,
				V: V,
				R: R,
				S: S,
			}
		}

		if type_ == types.AccessListTxType || type_ == types.DynamicFeeTxType {
			//TODO: handle accesslisttxs
		}


		log.Trace("[backend.go/readTransactionsBatch] tx fetched", "tx", txdata)

		if seq != blocknumber_i {
			result[seq-uint64(start)] = txs
			seq = blocknumber_i
			txs = make([]*types.Transaction, 0)
		}

		tx := types.NewTx(txdata)
		txs = append(txs, tx)
	}

	if len(txs) > 0 {
		result[blocknumber_i-uint64(start)] = txs
	}

	timer_cpu_db_end := C.getCPUTimeNs()
	cputime := (uint64(timer_cpu_db_end) - uint64(timer_cpu_db_start))
	s.timer_cpu_db += cputime
	s.timer_cpu_db_tx += cputime

	return result, nil
}

// read uncles as a batch (hletrd)
func (s *Ethereum) readUnclesBatch(start int, end int) ([][]*types.Header, error) {
	timer_cpu_db_start := C.getCPUTimeNs()

	uncle_db, err := s.sql.Query("SELECT `blocknumber`, `uncleheight`, `timestamp`, `miner`, `difficulty`, `gasused`, `gaslimit`, `extradata`, `parenthash`, `sha3uncles`, `stateroot`, `nonce`, `receiptsroot`, `transactionsroot`, `mixhash`, `basefee`, `logsbloom` FROM `uncles` WHERE `blocknumber` >= ? AND `blocknumber` < ?", start, end)
	if err != nil {
		log.Error("[backend.go/readUnclesBatch] failed to fetch an uncle")
		return nil, ErrFetchUncles
	}
	defer uncle_db.Close()

	result := make([][]*types.Header, end - start)
	var uncles []*types.Header
	seq := uint64(start)

	blocknumber_i := uint64(start)
	var uncleheight_i uint64; var uncleheight *big.Int
	var timestamp uint64
	var miner_b []byte; var miner common.Address
	var difficulty_i uint64; var difficulty *big.Int
	var gasused uint64
	var gaslimit uint64
	var extradata []byte
	var parenthash_b []byte; var parenthash common.Hash
	var sha3uncles_b []byte; var sha3uncles common.Hash
	var stateroot_b []byte; var stateroot common.Hash
	var nonce_b []byte; var nonce types.BlockNonce
	var receiptsroot_b []byte; var receiptsroot common.Hash
	var transactionsroot_b []byte; var transactionsroot common.Hash
	var mixhash_b []byte; var mixhash common.Hash
	var basefee sql.NullInt64
	var logsbloom []byte

	for uncle_db.Next() {

		if err_ := uncle_db.Scan(&blocknumber_i, &uncleheight_i, &timestamp, &miner_b, &difficulty_i, &gasused, &gaslimit, &extradata, &parenthash_b, &sha3uncles_b, &stateroot_b, &nonce_b, &receiptsroot_b, &transactionsroot_b, &mixhash_b, &basefee, &logsbloom); err_ != nil {
			log.Error("[backend.go/readUnclesBatch] failed to read an uncle", "number", blocknumber_i, "error", err)
			return nil, ErrFetchUncles
		}

		uncleheight = new(big.Int).SetUint64(uncleheight_i)
		miner = common.BytesToAddress(miner_b)
		difficulty = new(big.Int).SetUint64(difficulty_i)
		parenthash = common.BytesToHash(parenthash_b)
		sha3uncles = common.BytesToHash(sha3uncles_b)
		stateroot = common.BytesToHash(stateroot_b)
		nonce = types.EncodeNonce(binary.BigEndian.Uint64(nonce_b))
		receiptsroot = common.BytesToHash(receiptsroot_b)
		transactionsroot = common.BytesToHash(transactionsroot_b)
		mixhash = common.BytesToHash(mixhash_b)

		uncle := &types.Header{
			ParentHash: parenthash,
			UncleHash: sha3uncles,
			Coinbase: miner,
			Root: stateroot,
			TxHash: transactionsroot,
			ReceiptHash: receiptsroot,
			Bloom: types.BytesToBloom(logsbloom),
			Difficulty: difficulty,
			Number: uncleheight,
			GasLimit: gaslimit,
			GasUsed: gasused,
			Time: timestamp,
			Extra: extradata,
			MixDigest: mixhash,
			Nonce: nonce,
			BaseFee: nil,
		}

		if basefee.Valid {
			uncle.BaseFee = new(big.Int).SetUint64(uint64(basefee.Int64))
		}

		log.Trace("[backend.go/readUnclesBatch] uncle fetched", "block", blocknumber_i, "uncleheight", uncleheight)

		if seq != blocknumber_i {
			result[seq-uint64(start)] = uncles
			seq = blocknumber_i
			uncles = make([]*types.Header, 0)
		}

		uncles = append(uncles, uncle)
	}

	if len(uncles) > 0 {
		result[blocknumber_i-uint64(start)] = uncles
	}

	timer_cpu_db_end := C.getCPUTimeNs()
	cputime := (uint64(timer_cpu_db_end) - uint64(timer_cpu_db_start))
	s.timer_cpu_db += cputime
	s.timer_cpu_db_uncle += cputime

	return result, nil
}

// read a block from the database (hletrd)
func (s *Ethereum) readBlock(number int) (*types.Header, error) {
	result, err := s.readBlockBatch(number, number+1)
	return result[0], err
}

// read txs from the database (hletrd)
func (s *Ethereum) readTransactions(blocknumber int) ([]*types.Transaction, error) {
	result, err := s.readTransactionsBatch(blocknumber, blocknumber+1)
	return result[0], err
}

// read uncles from the database (hletrd)
func (s *Ethereum) readUncles(blocknumber int) ([]*types.Header, error) {
	result, err := s.readUnclesBatch(blocknumber, blocknumber+1)
	return result[0], err
}

// insertChain handler for goroutine (hletrd)
func (s *Ethereum) insertChain(chain []*types.Block, result chan bool) {
	// TODO: check if this cgocall is thread-safe and work properly
	timer_cpu_insert_start := C.getCPUTimeNs()

	s.config.Ethash.PowMode = ethash.ModeFullFake
	index, err := s.blockchain.InsertChainPlease(chain, s.config.Ethash.TxMetrics, s.config.Ethash.TxMetricsPath)
	_ = index
	s.config.Ethash.PowMode = ethash.ModeNormal
	if err != nil {
		log.Error("[backend.go/insertChain] failed to insert blocks", "err", err)
		result <- false
		return
	}
	result <- true

	timer_cpu_insert_end := C.getCPUTimeNs()
	cputime := (uint64(timer_cpu_insert_end) - uint64(timer_cpu_insert_start))
	s.timer_cpu_insert += cputime
}

// insert multiple blocks (hletrd)
func (s *Ethereum) insertBlockRange(start int, end int) bool {
	if end <= start {
		log.Error("[backend.go/insertBlockRange] end must be greater than start")
		return false
	}

	s.handler.downloader.Cancel()

	if s.sql == nil {
		log.Error("[backend.go/insertBlockRange] not connected to an SQL server")
		return false
	}

	batchsize := 1000

	blocks := make([]*types.Block, batchsize)
	//seq := 0
	inserting := false

	result_ch := make(chan bool)

	for number := start; number < end; number+=batchsize {
		end_batch := number+batchsize
		if end_batch > end {
			end_batch = end
		}

		header, err := s.readBlockBatch(number, end_batch)
		if err != nil {
			return false
		}

		txs, err := s.readTransactionsBatch(number, end_batch)
		if err != nil {
			return false
		}

		uncles, err := s.readUnclesBatch(number, end_batch)
		if err != nil {
			return false
		}

		for i := 0; i < end_batch-number; i++ {
			block := types.NewBlockWithHeader(header[i]).WithBody(txs[i], uncles[i])
			blockhash := block.Hash()
			blocksize := block.Size()

			log.Trace("[backend.go/insertBlockRange] block prepared", "block", block, "header", header, "hash", blockhash, "size", blocksize, "txs", txs[i], "uncles", uncles[i])
			blocks[i] = block
		}

		log.Trace("[backend.go/insertBlockRange] block insert")
		if inserting == true {
			result := <- result_ch
			if result == false {
				log.Error("[backend.go/insertBlockRange] insert failed")
				return false
			}
		}
		blocks_insert := make([]*types.Block, end_batch-number)
		copy(blocks_insert, blocks[:end_batch-number])
		go s.insertChain(blocks_insert, result_ch)
		inserting = true
	}

	if inserting == true {
		result := <- result_ch
		if result == false {
			log.Error("[backend.go/insertBlockRange] insert failed")
			return false
		}
	}

	log.Trace("[backend.go/insertBlockRange] inserted blocks", "start", start, "end", end)
	return true
}

// insert a single block, actually implemented via insertBlockRange (hletrd)
func (s *Ethereum) insertBlock(number int) bool {
	return s.insertBlockRange(number, number+1)
}