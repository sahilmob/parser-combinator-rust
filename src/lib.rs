type ParseResult<'a, Output> = Result<(&'a str, Output), ParserError<'a>>;
type Parser<'a, Output> = dyn Fn(&'a str) -> ParseResult<'a, Output>;

type ParserError<'a> = (&'a str, String);

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
}
