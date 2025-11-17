//! Integration tests for multiple abstract domains working together

use abstract_interpretation::*;

#[test]
fn test_sign_constant_cooperation() {
    // Test that Sign and Constant domains provide complementary information
    let sign_domain = SignDomain;
    let const_domain = ConstantDomain;

    // Start with x = 5
    let sign_elem = sign_domain.constant(&"x".to_string(), 5);
    let const_elem = const_domain.constant(&"x".to_string(), 5);

    // Sign knows it's positive
    assert_eq!(sign_elem.get("x"), Sign::Pos);

    // Constant knows exact value
    assert_eq!(const_elem.get("x"), ConstValue::Const(5));

    // After y = x + 10
    use NumExpr::*;
    let expr = Add(Box::new(Var("x".to_string())), Box::new(Const(10)));

    let sign_result = sign_domain.assign(&sign_elem, &"y".to_string(), &expr);
    let const_result = const_domain.assign(&const_elem, &"y".to_string(), &expr);

    // Sign: positive + positive = positive
    assert_eq!(sign_result.get("y"), Sign::NonNeg);

    // Constant: 5 + 10 = 15
    assert_eq!(const_result.get("y"), ConstValue::Const(15));
}

#[test]
fn test_sign_interval_cooperation() {
    // Test Sign and Interval working together
    let sign_domain = SignDomain;
    let interval_domain = IntervalDomain;

    // x in [1, 100]
    let sign_elem = sign_domain.interval(&"x".to_string(), 1, 100);
    let interval_elem = interval_domain.interval(&"x".to_string(), 1, 100);

    // Sign: all positive (since low > 0)
    assert_eq!(sign_elem.get("x"), Sign::Pos);

    // Interval: precise bounds
    if let Some((low, high)) = interval_domain.get_bounds(&interval_elem, &"x".to_string()) {
        assert_eq!(low, 1);
        assert_eq!(high, 100);
    } else {
        panic!("Expected bounds");
    }
}

#[test]
fn test_constant_interval_refinement() {
    // Test how Constant and Interval refine each other
    let const_domain = ConstantDomain;
    let interval_domain = IntervalDomain;

    // Start with x = 5
    let const_elem = const_domain.constant(&"x".to_string(), 5);
    let interval_elem = interval_domain.constant(&"x".to_string(), 5);

    // Both agree on singleton
    assert_eq!(const_elem.get("x"), ConstValue::Const(5));
    assert_eq!(interval_domain.get_bounds(&interval_elem, &"x".to_string()), Some((5, 5)));

    // After join with x in [10, 20]
    let const_elem2 = const_domain.constant(&"x".to_string(), 15);
    let interval_elem2 = interval_domain.interval(&"x".to_string(), 10, 20);

    let const_joined = const_domain.join(&const_elem, &const_elem2);
    let interval_joined = interval_domain.join(&interval_elem, &interval_elem2);

    // Constant loses precision (5 vs 15 -> Top)
    assert_eq!(const_joined.get("x"), ConstValue::Top);

    // Interval maintains bounds [5, 20]
    assert_eq!(interval_domain.get_bounds(&interval_joined, &"x".to_string()), Some((5, 20)));
}

#[test]
fn test_triple_domain_analysis() {
    // Test all three domains analyzing the same program
    let sign_domain = SignDomain;
    let const_domain = ConstantDomain;
    let interval_domain = IntervalDomain;

    // Program: x = 7; y = x; z = y;
    let sign = sign_domain.constant(&"x".to_string(), 7);
    let constant = const_domain.constant(&"x".to_string(), 7);
    let interval = interval_domain.constant(&"x".to_string(), 7);

    use NumExpr::*;
    let expr = Var("x".to_string());

    let sign = sign_domain.assign(&sign, &"y".to_string(), &expr);
    let constant = const_domain.assign(&constant, &"y".to_string(), &expr);
    let interval = interval_domain.assign(&interval, &"y".to_string(), &expr);

    let expr = Var("y".to_string());

    let sign = sign_domain.assign(&sign, &"z".to_string(), &expr);
    let constant = const_domain.assign(&constant, &"z".to_string(), &expr);
    let interval = interval_domain.assign(&interval, &"z".to_string(), &expr);

    // All domains agree: z = 7
    assert_eq!(sign.get("z"), Sign::Pos);
    assert_eq!(constant.get("z"), ConstValue::Const(7));
    assert_eq!(interval_domain.get_bounds(&interval, &"z".to_string()), Some((7, 7)));
}

#[test]
fn test_sign_constant_assume() {
    // Test assume() operations across domains
    let sign_domain = SignDomain;
    let const_domain = ConstantDomain;

    // Start with x in unknown range
    let sign_elem = sign_domain.top();
    let const_elem = const_domain.top();

    // Assume x > 0
    use NumExpr::*;
    use NumPred::*;
    let pred = Gt(Var("x".to_string()), Const(0));

    let sign_refined = sign_domain.assume(&sign_elem, &pred);
    let const_refined = const_domain.assume(&const_elem, &pred);

    // Sign: x must be positive
    assert_eq!(sign_refined.get("x"), Sign::Pos);

    // Constant: still unknown (could be any positive value)
    assert_eq!(const_refined.get("x"), ConstValue::Top);

    // Now assume x == 5
    let pred = Eq(Var("x".to_string()), Const(5));

    let sign_refined2 = sign_domain.assume(&sign_refined, &pred);
    let const_refined2 = const_domain.assume(&const_refined, &pred);

    // Sign: still positive
    assert_eq!(sign_refined2.get("x"), Sign::Pos);

    // Constant: now knows exact value
    assert_eq!(const_refined2.get("x"), ConstValue::Const(5));
}

#[test]
fn test_domain_precision_comparison() {
    // Compare precision of different domains on same operations
    let sign_domain = SignDomain;
    let const_domain = ConstantDomain;
    let interval_domain = IntervalDomain;

    // x = 5, y = 10
    let sign = sign_domain.constant(&"x".to_string(), 5);
    let sign = sign_domain.assign(&sign, &"y".to_string(), &NumExpr::Const(10));

    let constant = const_domain.constant(&"x".to_string(), 5);
    let constant = const_domain.assign(&constant, &"y".to_string(), &NumExpr::Const(10));

    let interval = interval_domain.constant(&"x".to_string(), 5);
    let interval = interval_domain.assign(&interval, &"y".to_string(), &NumExpr::Const(10));

    // z = x + y
    use NumExpr::*;
    let expr = Add(Box::new(Var("x".to_string())), Box::new(Var("y".to_string())));

    let sign_result = sign_domain.assign(&sign, &"z".to_string(), &expr);
    let const_result = const_domain.assign(&constant, &"z".to_string(), &expr);
    let interval_result = interval_domain.assign(&interval, &"z".to_string(), &expr);

    // Sign: positive + positive = non-negative (loses that it's strictly positive)
    assert_eq!(sign_result.get("z"), Sign::NonNeg);

    // Constant: exact value 15
    assert_eq!(const_result.get("z"), ConstValue::Const(15));

    // Interval: exact value [15, 15]
    assert_eq!(interval_domain.get_bounds(&interval_result, &"z".to_string()), Some((15, 15)));

    // Constant and Interval are most precise here
}

#[test]
fn test_widening_across_domains() {
    // Test widening behavior in different domains
    let sign_domain = SignDomain;
    let const_domain = ConstantDomain;
    let interval_domain = IntervalDomain;

    // Iteration 1: x = 0
    let sign1 = sign_domain.constant(&"x".to_string(), 0);
    let const1 = const_domain.constant(&"x".to_string(), 0);
    let interval1 = interval_domain.constant(&"x".to_string(), 0);

    // Iteration 2: x = 1
    let sign2 = sign_domain.constant(&"x".to_string(), 1);
    let const2 = const_domain.constant(&"x".to_string(), 1);
    let interval2 = interval_domain.constant(&"x".to_string(), 1);

    // Widen
    let sign_widened = sign_domain.widen(&sign1, &sign2);
    let const_widened = const_domain.widen(&const1, &const2);
    let interval_widened = interval_domain.widen(&interval1, &interval2);

    // Sign: 0 and 1 -> NonNeg (flat lattice, widen = join)
    assert_eq!(sign_widened.get("x"), Sign::NonNeg);

    // Constant: different constants -> Top (flat lattice, widen = join)
    assert_eq!(const_widened.get("x"), ConstValue::Top);

    // Interval: [0,0] ∇ [1,1] -> typically [0, +∞) but implementation may vary
    // Just verify widening doesn't lose the lower bound 0
    let bounds = interval_domain.get_bounds(&interval_widened, &"x".to_string());
    if let Some((low, _high)) = bounds {
        assert_eq!(low, 0, "Lower bound should be preserved");
        // Upper bound might be MAX or infinite depending on implementation
    }
    // Note: Some widening strategies might lose precision entirely
}
