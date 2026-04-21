use std::collections::BTreeMap;

use tower_lsp::lsp_types::{Position, Range};

use crate::elaborator::named_entity::NamedEntity;
use crate::syntax::token::Token;

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct TokenKey {
    pub line_number: u32,
    pub start: u32,
    pub len: u32,
}

impl TokenKey {
    pub fn new(line_number: u32, start: u32, len: u32) -> Self {
        TokenKey {
            line_number,
            start,
            len,
        }
    }

    fn contains(&self, line_number: u32, position: u32) -> bool {
        self.line_number == line_number
            && position >= self.start
            && position < self.start + self.len
    }

    pub fn range(&self) -> Range {
        Range {
            start: Position {
                line: self.line_number as u32,
                character: self.start,
            },
            end: Position {
                line: self.line_number as u32,
                character: self.start + self.len,
            },
        }
    }
}

/// Information stored about a token in the source code.
#[derive(Clone, Debug, PartialEq)]
pub struct TokenInfo {
    /// The text of the actual token.
    pub text: String,

    /// The entity that this token refers to.
    pub entity: NamedEntity,
}

/// A map from tokens to TokenInfo values.
///
/// This assumes that tokens do not overlap - each position in the source
/// can belong to at most one token.
/// It doesn't enforce this, though.
#[derive(Clone)]
pub struct TokenMap {
    map: BTreeMap<TokenKey, TokenInfo>,
}

impl TokenMap {
    pub fn new() -> Self {
        TokenMap {
            map: BTreeMap::new(),
        }
    }

    pub fn insert(&mut self, token: &Token, value: TokenInfo) {
        let key = TokenKey::new(token.line_number, token.start, token.len);

        #[cfg(test)]
        {
            // INTENTIONAL: This duplicate detection is deliberate and should NOT be removed.
            // We want tests to fail when the same token is tracked multiple times,
            // as this indicates a bug in the token tracking logic.
            // DO NOT add logic to silently skip duplicates - fix the root cause instead.
            if let Some(existing) = self.map.get(&key) {
                panic!(
                    "Duplicate token insertion detected!\n\
                     Token: '{}' at line {}, start {}, len {}\n\
                     Existing: {:?}\n\
                     New: {:?}",
                    value.text, key.line_number, key.start, key.len, existing, value
                );
            }
        }

        self.map.insert(key, value);
    }

    /// Track a token with its associated entity.
    pub fn track_token(&mut self, token: &Token, entity: &NamedEntity) {
        let info = TokenInfo {
            text: token.text().to_string(),
            entity: entity.clone(),
        };
        self.insert(token, info);
    }

    /// Get the token that contains the given position, if any.
    ///
    /// This uses the fact that if a token contains (line_number, position),
    /// it must be the last token that starts at or before that position on that line.
    pub fn get(&self, line_number: u32, position: u32) -> Option<(&TokenKey, &TokenInfo)> {
        // Create a key representing the position we're looking for
        let search_key = TokenKey::new(line_number, position + 1, 0);

        // Find the last entry with key < search_key
        // This gives us the last token that starts at or before the position
        let range = self.map.range(..search_key);
        if let Some((key, value)) = range.last() {
            // Check if this token actually contains the position
            if key.contains(line_number, position) {
                return Some((key, value));
            }
        }

        None
    }

    pub fn iter(&self) -> impl Iterator<Item = (&TokenKey, &TokenInfo)> {
        self.map.iter()
    }
}

impl Default for TokenMap {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::elaborator::acorn_value::AcornValue;
    use crate::elaborator::named_entity::NamedEntity;

    fn test_token_info(text: &str) -> TokenInfo {
        TokenInfo {
            text: text.to_string(),
            entity: NamedEntity::Value(AcornValue::Bool(true)),
        }
    }

    #[test]
    fn test_token_map_lookups() {
        let mut map = TokenMap::new();

        // Add some tokens with various positions
        // Line 1: tokens at positions 0-3, 5-8, 10-12
        map.insert(&Token::test_token(1, 0, 3), test_token_info("first"));
        map.insert(&Token::test_token(1, 5, 3), test_token_info("second"));
        map.insert(&Token::test_token(1, 10, 2), test_token_info("third"));

        // Line 2: tokens at positions 2-7, 8-9, 15-20
        map.insert(&Token::test_token(2, 2, 5), test_token_info("fourth"));
        map.insert(&Token::test_token(2, 8, 1), test_token_info("fifth"));
        map.insert(&Token::test_token(2, 15, 5), test_token_info("sixth"));

        // Line 5: tokens at positions 0-10, 12-15
        map.insert(&Token::test_token(5, 0, 10), test_token_info("seventh"));
        map.insert(&Token::test_token(5, 12, 3), test_token_info("eighth"));

        // Line 10: single token at 5-8
        map.insert(&Token::test_token(10, 5, 3), test_token_info("ninth"));

        // Line 15: token at position 0-1
        map.insert(&Token::test_token(15, 0, 1), test_token_info("tenth"));

        // Test lookups that should find tokens
        assert_eq!(
            map.get(1, 0).map(|(_, v)| &v.text),
            Some(&"first".to_string())
        );
        assert_eq!(
            map.get(1, 2).map(|(_, v)| &v.text),
            Some(&"first".to_string())
        );
        assert_eq!(
            map.get(1, 5).map(|(_, v)| &v.text),
            Some(&"second".to_string())
        );
        assert_eq!(
            map.get(1, 7).map(|(_, v)| &v.text),
            Some(&"second".to_string())
        );
        assert_eq!(
            map.get(1, 10).map(|(_, v)| &v.text),
            Some(&"third".to_string())
        );
        assert_eq!(
            map.get(1, 11).map(|(_, v)| &v.text),
            Some(&"third".to_string())
        );

        assert_eq!(
            map.get(2, 3).map(|(_, v)| &v.text),
            Some(&"fourth".to_string())
        );
        assert_eq!(
            map.get(2, 6).map(|(_, v)| &v.text),
            Some(&"fourth".to_string())
        );
        assert_eq!(
            map.get(2, 8).map(|(_, v)| &v.text),
            Some(&"fifth".to_string())
        );
        assert_eq!(
            map.get(2, 17).map(|(_, v)| &v.text),
            Some(&"sixth".to_string())
        );

        assert_eq!(
            map.get(5, 0).map(|(_, v)| &v.text),
            Some(&"seventh".to_string())
        );
        assert_eq!(
            map.get(5, 9).map(|(_, v)| &v.text),
            Some(&"seventh".to_string())
        );
        assert_eq!(
            map.get(5, 12).map(|(_, v)| &v.text),
            Some(&"eighth".to_string())
        );
        assert_eq!(
            map.get(5, 14).map(|(_, v)| &v.text),
            Some(&"eighth".to_string())
        );

        assert_eq!(
            map.get(10, 6).map(|(_, v)| &v.text),
            Some(&"ninth".to_string())
        );
        assert_eq!(
            map.get(15, 0).map(|(_, v)| &v.text),
            Some(&"tenth".to_string())
        );

        // Test lookups that should not find tokens (gaps between tokens)
        assert_eq!(map.get(1, 3), None);
        assert_eq!(map.get(1, 4), None);
        assert_eq!(map.get(1, 8), None);
        assert_eq!(map.get(1, 9), None);
        assert_eq!(map.get(1, 12), None);

        assert_eq!(map.get(2, 0), None);
        assert_eq!(map.get(2, 1), None);
        assert_eq!(map.get(2, 7), None);
        assert_eq!(map.get(2, 9), None);
        assert_eq!(map.get(2, 10), None);
        assert_eq!(map.get(2, 14), None);
        assert_eq!(map.get(2, 20), None);

        assert_eq!(map.get(5, 10), None);
        assert_eq!(map.get(5, 11), None);
        assert_eq!(map.get(5, 15), None);

        assert_eq!(map.get(10, 0), None);
        assert_eq!(map.get(10, 4), None);
        assert_eq!(map.get(10, 8), None);

        assert_eq!(map.get(15, 1), None);

        // Test lookups on lines with no tokens
        assert_eq!(map.get(3, 0), None);
        assert_eq!(map.get(3, 10), None);
        assert_eq!(map.get(4, 5), None);
        assert_eq!(map.get(20, 0), None);
    }

    #[test]
    fn test_token_key_ordering() {
        // Verify that TokenKey ordering works as expected
        let key1 = TokenKey::new(1, 0, 5);
        let key2 = TokenKey::new(1, 5, 3);
        let key3 = TokenKey::new(1, 10, 2);
        let key4 = TokenKey::new(2, 0, 5);
        let key5 = TokenKey::new(2, 5, 3);

        assert!(key1 < key2);
        assert!(key2 < key3);
        assert!(key3 < key4);
        assert!(key4 < key5);

        // Same line and start, different lengths
        let key_a = TokenKey::new(1, 5, 3);
        let key_b = TokenKey::new(1, 5, 5);
        assert!(key_a < key_b);
    }
}
