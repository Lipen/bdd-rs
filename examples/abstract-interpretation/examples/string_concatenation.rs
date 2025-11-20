use abstract_interpretation::*;

fn main() {
    println!("=== String Concatenation Analysis ===");
    println!("This example demonstrates analyzing string lengths during concatenation.");
    println!("Scenario: Constructing a URL from parts and verifying its length.");

    let domain = StringLengthDomain::new();
    let mut state = domain.top();

    // 1. Define parts of a URL
    println!("\n--- Step 1: Define URL Parts ---");
    println!("Program:");
    println!("  protocol = \"https://\"");
    println!("  domain = \"example.com\"");
    println!("  path = \"/api/v1\"");

    // protocol = "https://" (len 8)
    state = domain.assign_const(&state, "protocol", "https://");

    // domain = "example.com" (len 11)
    state = domain.assign_const(&state, "domain", "example.com");

    // path = "/api/v1" (len 7)
    state = domain.assign_const(&state, "path", "/api/v1");

    println!("\nAnalysis Results:");
    let len_proto = domain.get_length(&state, "protocol");
    println!("  len(protocol): {}", len_proto);
    assert_eq!(len_proto, Interval::constant(8));

    let len_domain_var = domain.get_length(&state, "domain");
    println!("  len(domain):   {}", len_domain_var);
    assert_eq!(len_domain_var, Interval::constant(11));

    let len_path = domain.get_length(&state, "path");
    println!("  len(path):     {}", len_path);
    assert_eq!(len_path, Interval::constant(7));

    // 2. Build full URL
    println!("\n--- Step 2: Build Full URL ---");
    println!("Program:");
    println!("  url = protocol + domain + path");

    // url = protocol + domain
    state = domain.assign_concat(&state, "temp", "protocol", "domain");
    // url = temp + path
    state = domain.assign_concat(&state, "url", "temp", "path");

    let url_len = domain.get_length(&state, "url");
    println!("\nAnalysis Results:");
    println!("  len(url): {}", url_len);

    // Expected length: 8 + 11 + 7 = 26
    assert_eq!(url_len, Interval::constant(26));
    println!("  ✓ Verified: URL length is exactly 26."); // 3. Variable length part
    println!("\n--- Step 3: Variable Length Analysis ---");
    println!("Program:");
    println!("  assume(0 <= len(query) <= 100)");
    println!("  full_url = url + query");

    // query = input() (assume length 0 to 100)
    let query_len_pred = NumPred::And(
        Box::new(NumPred::Ge(NumExpr::Var("query".to_string()), NumExpr::Const(0))),
        Box::new(NumPred::Le(NumExpr::Var("query".to_string()), NumExpr::Const(100))),
    );
    state = domain.assume_length(&state, &query_len_pred);
    println!("\nAnalysis Results:");
    println!("  len(query): {}", domain.get_length(&state, "query"));

    // full_url = url + query
    state = domain.assign_concat(&state, "full_url", "url", "query");

    let full_len = domain.get_length(&state, "full_url");
    println!("  len(full_url): {}", full_len);

    // Expected: [26, 126]
    assert_eq!(full_len, Interval::new(Bound::Finite(26), Bound::Finite(126)));
    println!("  ✓ Verified: Full URL length is in [26, 126].");
}
