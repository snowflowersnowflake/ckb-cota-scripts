# ckb-cota-scripts

[![License](https://img.shields.io/badge/license-MIT-green)](https://github.com/nervina-labs/ckb-cota-scripts/blob/develop/COPYING)
[![Github Actions CI](https://github.com/nervina-labs/ckb-cota-scripts/workflows/CI/badge.svg?branch=develop)](https://github.com/nervina-labs/ckb-cota-scripts/actions)

The Compact Token Aggregator Standard type scripts implement of [[RFC] CoTA: A Compact Token Aggregator Standard for Extremely Low Cost NFTs and FTs](https://talk.nervos.org/t/rfc-cota-a-compact-token-aggregator-standard-for-extremely-low-cost-nfts-and-fts/6338) on [Nervos CKB](https://www.nervos.org/).

## Pre-requirement

- [capsule](https://github.com/nervosnetwork/capsule) >= 0.7.1
- [ckb-cli](https://github.com/nervosnetwork/ckb-cli) >= 0.100.0

> Note: Capsule uses docker to build contracts and run tests. https://docs.docker.com/get-docker/
> and docker and ckb-cli must be accessible in the PATH in order for them to be used by Capsule.

## Getting Started

Build contracts:

```sh
make build
```

Run tests:

```sh
make test
```

## Deployment

### 1. Update the deployment configurations

Update the `deployment.toml` referring to the [Capsule Docs](https://docs.nervos.org/docs/labs/sudtbycapsule#deploy)

### 2. Build release version of the script

The release version of script doesn’t include debug symbols which makes the size smaller.

```sh
make build-release
```

### 3. Deploy the scripts

```sh
capsule deploy --address <ckt1....> --fee 0.001
```


