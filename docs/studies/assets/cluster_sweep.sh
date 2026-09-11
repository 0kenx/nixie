#!/usr/bin/env bash
# Cluster sweep: remaining nixie-unknown cells (z3 decides most), 60s cap.
set -u
NIXIE=/media/data/proj/nixie/target/release/nixie
ROOT=/media/data/proj/nixie/smt-lib/non-incremental/QF_BV
run() { # file z3verdict
  local F=$1 Z=$2
  local OUT=$( { time taskset -c 10 timeout 70 $NIXIE -t 60 "$F" ; } 2>&1 | rg '^(unsat|sat|unknown)|real' | tr '\n' ' ' )
  echo "$Z | $OUT| $(basename $F)"
}
cd "$ROOT"
for P in 2468:sat 1804:unsat 988:unsat 2710:unsat 1963:unknown; do
  F=${P%%:*}; Z=${P##*:}
  run "20210219-Sydr/master/cjpeg/predicate_$F.smt2" "$Z"
done
for P in s3_clnt_1_true.BV.c.cil.c.21:unsat s3_clnt_2_false.BV.c.cil.c.21:sat s3_clnt_3_true.BV.c.cil.c.21:unsat s3_clnt_3_false.BV.c.cil.c.17:sat; do
  F=${P%%:*}; Z=${P##*:}
  run "bmc-bv-svcomp14/$F.smt2" "$Z"
done
run "20210219-Sydr/symbolic_memory/bst/hdp/predicate_3365.smt2" unsat
run "20210219-Sydr/symbolic_memory/linear/readelf/predicate_2300.smt2" unknown
run "spear/samba_v3.0.24/bin_libmsrpc_vc1232059.smt2" sat
run "spear/samba_v3.0.24/bin_libsmbsharemodes_vc6344.smt2" sat
run "spear/samba_v3.0.24/bin_libsmbsharemodes_vc7692.smt2" sat
run "spear/samba_v3.0.24/bin_libsmbsharemodes_vc4817.smt2" sat
