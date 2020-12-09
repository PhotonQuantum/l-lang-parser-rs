pub fn indent(input_str: &str) -> String {
    input_str
        .lines()
        .into_iter()
        .map(|x| format!("  {}", x))
        .fold_first(|x, y| format!("{}\n{}", x, y))
        .unwrap_or(String::new())
}
