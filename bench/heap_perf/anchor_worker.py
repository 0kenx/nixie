#!/usr/bin/env python3
"""The original independent worker, extended only with authenticated case oracles."""
import run
import anchor_cases

if __name__ == '__main__':
    run.oracle = anchor_cases.oracle
    run.main()
