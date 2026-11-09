use nixie_solver::Context;

fn pigeonhole(pigeons: usize, holes: usize) -> String {
    let mut script = String::from("(set-logic QF_UF)\n");
    for p in 0..pigeons {
        for h in 0..holes {
            script.push_str(&format!("(declare-const p{p}h{h} Bool)\n"));
        }
        script.push_str("(assert (or");
        for h in 0..holes {
            script.push_str(&format!(" p{p}h{h}"));
        }
        script.push_str("))\n");
    }
    for h in 0..holes {
        for p in 0..pigeons {
            for q in p + 1..pigeons {
                script.push_str(&format!("(assert (or (not p{p}h{h}) (not p{q}h{h})))\n"));
            }
        }
    }
    script
}

#[test]
fn decision_allowance_rearms_then_clears_on_the_same_context() {
    let mut ctx = Context::new();
    ctx.execute_script(&pigeonhole(7, 6)).unwrap();
    ctx.execute_script("(set-option :max-decisions 1)").unwrap();
    for round in 0..3 {
        // Changing the setting invalidates the verdict cache, so each query
        // must search and receive its own allowance over cumulative counters.
        let allowance = round + 1;
        let before = ctx.stats().decisions;
        let output = ctx
            .execute_script(&format!(
                "(set-option :max-decisions {allowance})(check-sat)"
            ))
            .unwrap();
        assert_eq!(output, ["unknown"]);
        let spent = ctx.stats().decisions - before;
        assert!(spent > 0 && spent <= allowance, "query {round}: {spent}");
    }
    assert_eq!(
        ctx.execute_script("(set-option :max-decisions 0)(check-sat)")
            .unwrap(),
        ["unsat"]
    );
}

#[test]
fn embedded_check_option_limits_work_and_can_be_cleared() {
    let mut ctx = Context::new();
    ctx.execute_script(
        "(set-logic QF_BV)
         (declare-const x (_ BitVec 8))
         (push 1)
         (assert (bvult x #x80))
         (set-option :max-bv-embedded-checks 1)",
    )
    .unwrap();
    assert_eq!(ctx.execute_script("(check-sat)").unwrap(), ["unknown"]);
    let stats = ctx.get_statistics();
    let words: Vec<_> = stats.trim_matches(['(', ')']).split_whitespace().collect();
    assert!(
        words
            .windows(2)
            .any(|pair| pair == [":bv-embedded-checks", "2"])
    );
    assert_eq!(
        ctx.execute_script("(set-option :max-bv-embedded-checks 0)(check-sat)")
            .unwrap(),
        ["sat"]
    );
}

#[test]
fn conflict_allowance_is_relative_to_each_query() {
    let mut ctx = Context::new();
    ctx.execute_script(&pigeonhole(7, 6)).unwrap();
    for allowance in 1..=3 {
        let before = ctx.stats().conflicts;
        assert_eq!(
            ctx.execute_script(&format!(
                "(set-option :max-conflicts {allowance})(check-sat)"
            ))
            .unwrap(),
            ["unknown"]
        );
        let spent = ctx.stats().conflicts - before;
        assert!(
            spent > 0 && spent <= allowance,
            "allowance {allowance}: {spent}"
        );
    }
    assert_eq!(
        ctx.execute_script("(set-option :max-conflicts 0)(check-sat)")
            .unwrap(),
        ["unsat"]
    );
}
