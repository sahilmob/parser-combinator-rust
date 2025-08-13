type ParseResult<'a, Output> = Result<(&'a str, Output), ParserError<'a>>;
type Parser<'a, Output> = dyn Fn(&'a str) -> ParseResult<'a, Output>;

type ParserError<'a> = (&'a str, String);

fn whitespace(source: &str) -> ParseResult<()> {
    let mut chars = source.chars();
    let mut end_index = 0;

    while chars.next().is_some_and(|c| c.is_whitespace()) {
        end_index += 1;
    }

    Ok((&source[end_index..], ()))
}

fn integer(source: &str) -> ParseResult<i64> {
    let mut chars = source.chars();
    let mut end_index = 0;

    if source.starts_with("-") {
        chars.next();
        end_index += 1;
    }

    while chars.next().is_some_and(|c| c.is_numeric()) {
        end_index += 1;
    }

    let parse_result = source[..end_index]
        .parse::<i64>()
        .map_err(|_| (source, "Expected integer".into()))?;

    Ok((&source[end_index..], parse_result))
}

fn literal<'a>(source: &'a str, target: &str) -> ParseResult<'a, ()> {
    source
        .strip_prefix(target)
        .ok_or((source, format!("Expected literal '{}'", target)))
        .map(|remainder| (remainder, ()))
}

fn valid_identifier(ch: char) -> bool {
    ch.is_alphabetic() || ch.is_numeric() || ch == '_'
}

fn identifier(source: &str) -> ParseResult<&str> {
    let mut chars = source.chars();
    let first = chars.next().ok_or((source, "Unexpected EOF".into()))?;

    if !first.is_alphabetic() {
        return Err((source, "Identifiers must begin with a letter".into()));
    }

    let start_index = 0;
    let mut end_index = 1;

    let mut next = chars.next();

    while next.is_some_and(valid_identifier) {
        next = chars.next();
        end_index += 1;
    }

    let id = &source[start_index..end_index];

    Ok((&source[end_index..], id))
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn parse_identifier() {
        let code = "variable = 3";
        let (remainder, identifier) = identifier(code).expect("Parsing failed");
        assert_eq!(identifier, "variable");
        assert_eq!(remainder, " = 3");
    }

    #[test]
    #[should_panic]
    fn parse_identifier_fails() {
        let code = "3variable = 3";
        let _ = identifier(code).unwrap();
    }

    #[test]
    fn parse_identifier_single() {
        let code = "v    = 3";
        let (remainder, identifier) = identifier(code).expect("Parsing failed");
        assert_eq!(identifier, "v");
        assert_eq!(remainder, "    = 3");
    }

    #[test]
    fn parse_literal() {
        let code = "= 3";
        let (remainder, value) = literal(code, "=").expect("Parsing failed");
        assert_eq!(value, ());
        assert_eq!(remainder, " 3");
    }

    #[test]
    fn parse_long_literal() {
        let code = "= 3";
        let (remainder, value) = literal(code, "= 3").expect("Parsing failed");
        assert_eq!(value, ());
        assert!(remainder.is_empty());
    }

    #[test]
    fn parse_integer() {
        let code = "3";
        let (remainder, value) = integer(code).expect("Parsing failed");
        assert_eq!(value, 3);
        assert!(remainder.is_empty());
    }

    #[test]
    fn parse_long_integer() {
        let code = "32232";
        let (remainder, value) = integer(code).expect("Parsing failed");
        assert_eq!(value, 32232);
        assert!(remainder.is_empty());
    }

    #[test]
    fn parse_negative_integer() {
        let code = "-3";
        let (remainder, value) = integer(code).expect("Parsing failed");
        assert_eq!(value, -3);
        assert!(remainder.is_empty());
    }

    #[test]
    fn parse_whitespace() {
        let code = "   -3";
        let (remainder, _value) = whitespace(code).expect("Parsing failed");
        assert_eq!(remainder, "-3");
    }
}
