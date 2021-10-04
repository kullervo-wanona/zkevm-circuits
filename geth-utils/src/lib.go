package main

import "C"
import (
	"encoding/json"
	"fmt"
	"math/big"
	"os"

	"github.com/ethereum/go-ethereum/common"
	"github.com/ethereum/go-ethereum/core/vm"
	"github.com/ethereum/go-ethereum/core/vm/runtime"
	"github.com/ethereum/go-ethereum/params"
)

//export CreateTrace
func CreateTrace(str_config string, str_code string) *C.char {

	var gethConfig GethConfig
	json.Unmarshal([]byte(str_config), &gethConfig)

	address := common.BytesToAddress([]byte{0xff})

	contracts := []Contract{{Address: address, Bytecode: []byte(str_code)}}

	logs, err := TraceTx(address, nil, &gethConfig.config, contracts)
	if err != nil {
		fmt.Fprintf(os.Stderr, "failed to trace tx, err: %v\n", err)
	}

	bytes, err := json.MarshalIndent(logs, "", "  ")
	if err != nil {
		fmt.Fprintf(os.Stderr, "failed to marshal logs, err: %v\n", err)
	}

	return C.CString(string(bytes))
}

type GethConfig struct {
	config runtime.Config
}

type JsonConfig struct {
	Hash        string `json:"hash"`
	Coinbase    string `json:"coinbase"`
	Timestamp   string `json:"timestamp"`
	BlockNumber string `json:"number"`
	Difficulty  string `json:"difficulty"`
	GasLimit    uint64 `json:"gas_limit,string"`
	ChainID     string `json:"chain_id"`
	BaseFee     string `json:"base_fee"`
}

func (this *GethConfig) UnmarshalJSON(b []byte) error {
	var jConfig JsonConfig
	err := json.Unmarshal(b, &jConfig)
	if err != nil {
		return err
	}

	this.config = runtime.Config{
		Origin:      common.BytesToAddress([]byte("origin")),
		GasLimit:    jConfig.GasLimit,
		Difficulty:  NewBigIntFromString(jConfig.Difficulty, 10),
		Time:        NewBigIntFromString(jConfig.Timestamp, 10),
		Coinbase:    AddressFromString(jConfig.Coinbase, 10),
		BlockNumber: NewBigIntFromString(jConfig.BlockNumber, 10),
		ChainConfig: &params.ChainConfig{
			ChainID:             NewBigIntFromString(jConfig.ChainID, 10),
			HomesteadBlock:      new(big.Int),
			ByzantiumBlock:      new(big.Int),
			ConstantinopleBlock: new(big.Int),
			DAOForkBlock:        new(big.Int),
			DAOForkSupport:      false,
			EIP150Block:         new(big.Int),
			EIP155Block:         new(big.Int),
			EIP158Block:         new(big.Int),
		},
		EVMConfig: vm.Config{},
	}

	return nil
}

func NewBigIntFromString(v string, base int) *big.Int {
	b, success := new(big.Int).SetString(v, base)
	if !success {
		fmt.Fprintf(os.Stderr, "failed to convert string '%s' to bigint\n", v)
		return nil
	}
	return b
}

func AddressFromString(v string, base int) common.Address {
	b := NewBigIntFromString(v, base)
	return common.BigToAddress(b)
}

func main() {}
