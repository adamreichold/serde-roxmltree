//! Convert [`roxmltree`] documents into [`serde`]-compatible types
//!
//! [Owned types][de::DeserializeOwned] can be deserialized directly from XML text using [`from_str`]:
//!
//! ```
//! use serde::Deserialize;
//! use serde_roxmltree::from_str;
//!
//! #[derive(Deserialize)]
//! struct Record {
//!     field: String,
//! }
//!
//! let record = from_str::<Record>("<record><field>foobar</field></record>")?;
//! assert_eq!(record.field, "foobar");
//! #
//! # Ok::<(), Box<dyn std::error::Error>>(())
//! ```
//!
//! [Borrowing types][de::Deserialize] must be deserialized from a [`Document`] using [`from_doc`]:
//!
//! ```
//! use roxmltree::Document;
//! use serde::Deserialize;
//! use serde_roxmltree::from_doc;
//!
//! #[derive(Deserialize)]
//! struct Record<'a> {
//!     field: &'a str,
//! }
//!
//! let document = Document::parse("<document><field>foobar</field></document>")?;
//!
//! let record = from_doc::<Record>(&document)?;
//! assert_eq!(record.field, "foobar");
//! #
//! # Ok::<(), Box<dyn std::error::Error>>(())
//! ```
//!
//! Fields of structures map to child elements and attributes:
//!
//! ```
//! use serde::Deserialize;
//! use serde_roxmltree::from_str;
//!
//! #[derive(Deserialize)]
//! struct Record {
//!     child: String,
//!     attribute: i32,
//! }
//!
//! let record = from_str::<Record>(r#"<record attribute="42"><child>foobar</child></record>"#)?;
//! assert_eq!(record.child, "foobar");
//! assert_eq!(record.attribute, 42);
//! #
//! # Ok::<(), Box<dyn std::error::Error>>(())
//! ```
//!
//! Sequences collect repeated child elements:
//!
//! ```
//! use serde::Deserialize;
//! use serde_roxmltree::from_str;
//!
//! #[derive(Deserialize)]
//! struct Record {
//!     field: Vec<String>,
//! }
//!
//! let record = from_str::<Record>("<record><field>foo</field><field>bar</field></record>")?;
//! assert_eq!(record.field, ["foo", "bar"]);
//! #
//! # Ok::<(), Box<dyn std::error::Error>>(())
//! ```
//!
//! Enum variants describe alternatives:
//!
//! ```
//! use serde::Deserialize;
//! use serde_roxmltree::from_str;
//!
//! #[derive(Debug, PartialEq, Deserialize)]
//! #[serde(rename_all = "lowercase")]
//! enum Record {
//!     Float(f32),
//!     Integer(i32),
//! }
//!
//! let record = from_str::<Record>("<record><float>42.0</float></record>")?;
//! assert_eq!(record, Record::Float(42.0));
//!
//! let record = from_str::<Record>("<record><integer>23</integer></record>")?;
//! assert_eq!(record, Record::Integer(23));
//! #
//! # Ok::<(), Box<dyn std::error::Error>>(())
//! ```
#![forbid(unsafe_code)]
#![deny(missing_docs)]
use std::char::ParseCharError;
use std::collections::HashSet;
use std::error::Error as StdError;
use std::fmt;
use std::iter::Peekable;
use std::num::{ParseFloatError, ParseIntError};
use std::str::{FromStr, ParseBoolError};

use roxmltree::{Attribute, Document, Error as XmlError, Node, NodeId};
use serde::de;

/// Deserialize an instance of type `T` directly from XML text
pub fn from_str<T>(text: &str) -> Result<T, Error>
where
    T: de::DeserializeOwned,
{
    let document = Document::parse(text).map_err(Error::ParseXml)?;
    from_doc(&document)
}

/// Deserialize an instance of type `T` from a [`roxmltree`] document
pub fn from_doc<'de, T>(document: &'de Document<'de>) -> Result<T, Error>
where
    T: de::Deserialize<'de>,
{
    let deserializer = Deserializer {
        source: Source::Node(document.root_element()),
        visited: &mut HashSet::new(),
    };
    T::deserialize(deserializer)
}

struct Deserializer<'de, 'tmp> {
    source: Source<'de>,
    visited: &'tmp mut HashSet<NodeId>,
}

#[derive(Clone, Copy, Debug)]
enum Source<'de> {
    Node(Node<'de, 'de>),
    Attribute(&'de Attribute<'de>),
}

impl<'de, 'tmp> Deserializer<'de, 'tmp> {
    fn name(&self) -> &'de str {
        match &self.source {
            Source::Node(node) => node.tag_name().name(),
            Source::Attribute(attr) => attr.name(),
        }
    }

    fn node(&self) -> Result<&Node<'de, 'de>, Error> {
        match &self.source {
            Source::Node(node) => Ok(node),
            Source::Attribute(_attr) => Err(Error::MissingNode),
        }
    }

    fn children_and_attributes(&self) -> Result<impl Iterator<Item = Source<'de>>, Error> {
        let node = self.node()?;

        Ok(node
            .children()
            .filter(|node| node.is_element())
            .map(Source::Node)
            .chain(node.attributes().iter().map(Source::Attribute)))
    }

    fn siblings(&self) -> Result<impl Iterator<Item = Node<'de, 'de>>, Error> {
        let node = self.node()?;

        let name = node.tag_name().name();

        Ok(node
            .next_siblings()
            .filter(move |node| node.tag_name().name() == name))
    }

    fn text(&self) -> &'de str {
        match self.source {
            Source::Node(node) => node.text().unwrap_or_default(),
            Source::Attribute(attr) => attr.value(),
        }
    }

    fn parse<T>(&self, err: fn(T::Err) -> Error) -> Result<T, Error>
    where
        T: FromStr,
    {
        self.text().trim().parse().map_err(err)
    }
}

impl<'de, 'tmp> de::Deserializer<'de> for Deserializer<'de, 'tmp> {
    type Error = Error;

    fn deserialize_bool<V>(self, visitor: V) -> Result<V::Value, Self::Error>
    where
        V: de::Visitor<'de>,
    {
        visitor.visit_bool(self.parse(Error::ParseBool)?)
    }

    fn deserialize_i8<V>(self, visitor: V) -> Result<V::Value, Self::Error>
    where
        V: de::Visitor<'de>,
    {
        visitor.visit_i8(self.parse(Error::ParseInt)?)
    }

    fn deserialize_i16<V>(self, visitor: V) -> Result<V::Value, Self::Error>
    where
        V: de::Visitor<'de>,
    {
        visitor.visit_i16(self.parse(Error::ParseInt)?)
    }

    fn deserialize_i32<V>(self, visitor: V) -> Result<V::Value, Self::Error>
    where
        V: de::Visitor<'de>,
    {
        visitor.visit_i32(self.parse(Error::ParseInt)?)
    }

    fn deserialize_i64<V>(self, visitor: V) -> Result<V::Value, Self::Error>
    where
        V: de::Visitor<'de>,
    {
        visitor.visit_i64(self.parse(Error::ParseInt)?)
    }

    fn deserialize_u8<V>(self, visitor: V) -> Result<V::Value, Self::Error>
    where
        V: de::Visitor<'de>,
    {
        visitor.visit_u8(self.parse(Error::ParseInt)?)
    }

    fn deserialize_u16<V>(self, visitor: V) -> Result<V::Value, Self::Error>
    where
        V: de::Visitor<'de>,
    {
        visitor.visit_u16(self.parse(Error::ParseInt)?)
    }

    fn deserialize_u32<V>(self, visitor: V) -> Result<V::Value, Self::Error>
    where
        V: de::Visitor<'de>,
    {
        visitor.visit_u32(self.parse(Error::ParseInt)?)
    }

    fn deserialize_u64<V>(self, visitor: V) -> Result<V::Value, Self::Error>
    where
        V: de::Visitor<'de>,
    {
        visitor.visit_u64(self.parse(Error::ParseInt)?)
    }

    fn deserialize_f32<V>(self, visitor: V) -> Result<V::Value, Self::Error>
    where
        V: de::Visitor<'de>,
    {
        visitor.visit_f32(self.parse(Error::ParseFloat)?)
    }

    fn deserialize_f64<V>(self, visitor: V) -> Result<V::Value, Self::Error>
    where
        V: de::Visitor<'de>,
    {
        visitor.visit_f64(self.parse(Error::ParseFloat)?)
    }

    fn deserialize_char<V>(self, visitor: V) -> Result<V::Value, Self::Error>
    where
        V: de::Visitor<'de>,
    {
        visitor.visit_char(self.parse(Error::ParseChar)?)
    }

    fn deserialize_str<V>(self, visitor: V) -> Result<V::Value, Self::Error>
    where
        V: de::Visitor<'de>,
    {
        visitor.visit_borrowed_str(self.text())
    }

    fn deserialize_string<V>(self, visitor: V) -> Result<V::Value, Self::Error>
    where
        V: de::Visitor<'de>,
    {
        self.deserialize_str(visitor)
    }

    fn deserialize_bytes<V>(self, _visitor: V) -> Result<V::Value, Self::Error>
    where
        V: de::Visitor<'de>,
    {
        Err(Error::NotSupported)
    }

    fn deserialize_byte_buf<V>(self, _visitor: V) -> Result<V::Value, Self::Error>
    where
        V: de::Visitor<'de>,
    {
        Err(Error::NotSupported)
    }

    fn deserialize_option<V>(self, visitor: V) -> Result<V::Value, Self::Error>
    where
        V: de::Visitor<'de>,
    {
        visitor.visit_some(self)
    }

    fn deserialize_unit<V>(self, visitor: V) -> Result<V::Value, Self::Error>
    where
        V: de::Visitor<'de>,
    {
        visitor.visit_unit()
    }

    fn deserialize_unit_struct<V>(
        self,
        _name: &'static str,
        visitor: V,
    ) -> Result<V::Value, Self::Error>
    where
        V: de::Visitor<'de>,
    {
        self.deserialize_unit(visitor)
    }

    fn deserialize_newtype_struct<V>(
        self,
        _name: &'static str,
        visitor: V,
    ) -> Result<V::Value, Self::Error>
    where
        V: de::Visitor<'de>,
    {
        visitor.visit_newtype_struct(self)
    }

    fn deserialize_seq<V>(self, visitor: V) -> Result<V::Value, Self::Error>
    where
        V: de::Visitor<'de>,
    {
        visitor.visit_seq(SeqAccess {
            source: self.siblings()?,
            visited: self.visited,
        })
    }

    fn deserialize_tuple<V>(self, _len: usize, visitor: V) -> Result<V::Value, Self::Error>
    where
        V: de::Visitor<'de>,
    {
        self.deserialize_seq(visitor)
    }

    fn deserialize_tuple_struct<V>(
        self,
        _name: &'static str,
        _len: usize,
        visitor: V,
    ) -> Result<V::Value, Self::Error>
    where
        V: de::Visitor<'de>,
    {
        self.deserialize_seq(visitor)
    }

    fn deserialize_map<V>(self, visitor: V) -> Result<V::Value, Self::Error>
    where
        V: de::Visitor<'de>,
    {
        visitor.visit_map(MapAccess {
            source: self.children_and_attributes()?.peekable(),
            visited: self.visited,
        })
    }

    fn deserialize_struct<V>(
        self,
        _name: &'static str,
        _fields: &'static [&'static str],
        visitor: V,
    ) -> Result<V::Value, Self::Error>
    where
        V: de::Visitor<'de>,
    {
        self.deserialize_map(visitor)
    }

    fn deserialize_enum<V>(
        self,
        _name: &'static str,
        _variants: &'static [&'static str],
        visitor: V,
    ) -> Result<V::Value, Self::Error>
    where
        V: de::Visitor<'de>,
    {
        visitor.visit_enum(EnumAccess {
            source: self.children_and_attributes()?,
            visited: self.visited,
        })
    }

    fn deserialize_identifier<V>(self, visitor: V) -> Result<V::Value, Self::Error>
    where
        V: de::Visitor<'de>,
    {
        visitor.visit_borrowed_str(self.name())
    }

    fn deserialize_any<V>(self, _visitor: V) -> Result<V::Value, Self::Error>
    where
        V: de::Visitor<'de>,
    {
        Err(Error::NotSupported)
    }

    fn deserialize_ignored_any<V>(self, visitor: V) -> Result<V::Value, Self::Error>
    where
        V: de::Visitor<'de>,
    {
        self.deserialize_unit(visitor)
    }
}

struct SeqAccess<'de, 'tmp, I>
where
    I: Iterator<Item = Node<'de, 'de>>,
{
    source: I,
    visited: &'tmp mut HashSet<NodeId>,
}

impl<'de, 'tmp, I> de::SeqAccess<'de> for SeqAccess<'de, 'tmp, I>
where
    I: Iterator<Item = Node<'de, 'de>>,
{
    type Error = Error;

    fn next_element_seed<T>(&mut self, seed: T) -> Result<Option<T::Value>, Self::Error>
    where
        T: de::DeserializeSeed<'de>,
    {
        match self.source.next() {
            None => Ok(None),
            Some(node) => {
                self.visited.insert(node.id());

                let deserializer = Deserializer {
                    source: Source::Node(node),
                    visited: &mut *self.visited,
                };
                seed.deserialize(deserializer).map(Some)
            }
        }
    }
}

struct MapAccess<'de, 'tmp, I>
where
    I: Iterator<Item = Source<'de>>,
{
    source: Peekable<I>,
    visited: &'tmp mut HashSet<NodeId>,
}

impl<'de, 'tmp, I> de::MapAccess<'de> for MapAccess<'de, 'tmp, I>
where
    I: Iterator<Item = Source<'de>>,
{
    type Error = Error;

    fn next_key_seed<K>(&mut self, seed: K) -> Result<Option<K::Value>, Self::Error>
    where
        K: de::DeserializeSeed<'de>,
    {
        loop {
            match self.source.peek() {
                None => return Ok(None),
                Some(source) => {
                    if let Source::Node(node) = source {
                        if self.visited.contains(&node.id()) {
                            self.source.next().unwrap();
                            continue;
                        }
                    }

                    let deserailizer = Deserializer {
                        source: *source,
                        visited: &mut *self.visited,
                    };
                    return seed.deserialize(deserailizer).map(Some);
                }
            }
        }
    }

    fn next_value_seed<V>(&mut self, seed: V) -> Result<V::Value, Self::Error>
    where
        V: de::DeserializeSeed<'de>,
    {
        let source = self.source.next().unwrap();

        let deserializer = Deserializer {
            source,
            visited: &mut *self.visited,
        };
        seed.deserialize(deserializer)
    }
}

struct EnumAccess<'de, 'tmp, I>
where
    I: Iterator<Item = Source<'de>>,
{
    source: I,
    visited: &'tmp mut HashSet<NodeId>,
}

impl<'de, 'tmp, I> de::EnumAccess<'de> for EnumAccess<'de, 'tmp, I>
where
    I: Iterator<Item = Source<'de>>,
{
    type Error = Error;
    type Variant = Deserializer<'de, 'tmp>;

    fn variant_seed<V>(mut self, seed: V) -> Result<(V::Value, Self::Variant), Self::Error>
    where
        V: de::DeserializeSeed<'de>,
    {
        let source = self.source.next().ok_or(Error::MissingChildOrAttribute)?;

        let deserializer = Deserializer {
            source,
            visited: &mut *self.visited,
        };
        let value = seed.deserialize(deserializer)?;

        let deserializer = Deserializer {
            source,
            visited: &mut *self.visited,
        };
        Ok((value, deserializer))
    }
}

impl<'de, 'tmp> de::VariantAccess<'de> for Deserializer<'de, 'tmp> {
    type Error = Error;

    fn unit_variant(self) -> Result<(), Self::Error> {
        Ok(())
    }

    fn newtype_variant_seed<T>(self, seed: T) -> Result<T::Value, Self::Error>
    where
        T: de::DeserializeSeed<'de>,
    {
        seed.deserialize(self)
    }

    fn tuple_variant<V>(self, len: usize, visitor: V) -> Result<V::Value, Self::Error>
    where
        V: de::Visitor<'de>,
    {
        de::Deserializer::deserialize_tuple(self, len, visitor)
    }

    fn struct_variant<V>(
        self,
        fields: &'static [&'static str],
        visitor: V,
    ) -> Result<V::Value, Self::Error>
    where
        V: de::Visitor<'de>,
    {
        de::Deserializer::deserialize_struct(self, "", fields, visitor)
    }
}

/// Possible errors when converting [`roxmltree`] documents to [`serde`]-compatible types
#[derive(Debug)]
pub enum Error {
    /// A node was expected, but an attribute was given
    MissingNode,
    /// At least one child or attribute is required
    MissingChildOrAttribute,
    /// An error when parsing XML
    ParseXml(XmlError),
    /// An error when parsing a boolean
    ParseBool(ParseBoolError),
    /// An error when parsing an integer
    ParseInt(ParseIntError),
    /// An error when parsing a floating point number
    ParseFloat(ParseFloatError),
    /// An error when parsing a character
    ParseChar(ParseCharError),
    /// The type is not supported
    NotSupported,
    /// A custom error produced by the type
    Custom(String),
}

impl de::Error for Error {
    fn custom<T: fmt::Display>(msg: T) -> Self {
        Self::Custom(msg.to_string())
    }
}

impl fmt::Display for Error {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Self::MissingNode => write!(fmt, "missing node"),
            Self::MissingChildOrAttribute => write!(fmt, "missing child or attribute"),
            Self::ParseXml(err) => write!(fmt, "XML parse error: {}", err),
            Self::ParseBool(err) => write!(fmt, "bool parse error: {}", err),
            Self::ParseInt(err) => write!(fmt, "int parse error: {}", err),
            Self::ParseFloat(err) => write!(fmt, "float parse error: {}", err),
            Self::ParseChar(err) => write!(fmt, "char parse error: {}", err),
            Self::NotSupported => write!(fmt, "not supported"),
            Self::Custom(msg) => write!(fmt, "custom error: {}", msg),
        }
    }
}

impl StdError for Error {}

#[cfg(test)]
mod tests {
    use super::*;

    use serde::Deserialize;

    #[test]
    fn parse_bool() {
        let val = from_str::<bool>("<root>false</root>").unwrap();
        assert!(!val);
        let val = from_str::<bool>("<root>\n\ttrue\n</root>").unwrap();
        assert!(val);

        let res = from_str::<bool>("<root>foobar</root>");
        assert!(matches!(res, Err(Error::ParseBool(_err))));
    }

    #[test]
    fn parse_char() {
        let val = from_str::<char>("<root>x</root>").unwrap();
        assert_eq!(val, 'x');
        let val = from_str::<char>("<root>\n\ty\n</root>").unwrap();
        assert_eq!(val, 'y');

        let res = from_str::<char>("<root>xyz</root>");
        assert!(matches!(res, Err(Error::ParseChar(_err))));
    }

    #[test]
    fn empty_text() {
        let val = from_str::<String>("<root></root>").unwrap();
        assert!(val.is_empty());
    }

    #[test]
    fn children_and_attributes() {
        #[derive(Deserialize)]
        struct Root {
            attr: i32,
            child: u64,
        }

        let val = from_str::<Root>(r#"<root attr="23"><child>42</child></root>"#).unwrap();
        assert_eq!(val.attr, 23);
        assert_eq!(val.child, 42);
    }

    #[test]
    fn multiple_children() {
        #[derive(Deserialize)]
        struct Root {
            child: Vec<i32>,
            another_child: String,
        }

        let val = from_str::<Root>(r#"<root><child>23</child><another_child>foobar</another_child><child>42</child></root>"#).unwrap();
        assert_eq!(val.child, [23, 42]);
        assert_eq!(val.another_child, "foobar");
    }

    #[test]
    fn multiple_lists_of_multiple_children() {
        #[derive(Deserialize)]
        struct Root {
            child: Vec<i32>,
            another_child: Vec<String>,
        }

        let val = from_str::<Root>(r#"<root><child>23</child><another_child>foo</another_child><child>42</child><another_child>bar</another_child></root>"#).unwrap();
        assert_eq!(val.child, [23, 42]);
        assert_eq!(val.another_child, ["foo", "bar"]);
    }

    #[test]
    fn zero_of_multiple_children() {
        #[derive(Deserialize)]
        struct Root {
            #[serde(default)]
            child: Vec<i32>,
        }

        let val = from_str::<Root>(r#"<root></root>"#).unwrap();
        assert_eq!(val.child, []);
    }

    #[test]
    fn optional_child() {
        #[derive(Deserialize)]
        struct Root {
            child: Option<f32>,
        }

        let val = from_str::<Root>(r#"<root><child>23.42</child></root>"#).unwrap();
        assert_eq!(val.child, Some(23.42));

        let val = from_str::<Root>(r#"<root></root>"#).unwrap();
        assert_eq!(val.child, None);
    }

    #[test]
    fn optional_attribute() {
        #[derive(Deserialize)]
        struct Root {
            attr: Option<f64>,
        }

        let val = from_str::<Root>(r#"<root attr="23.42"></root>"#).unwrap();
        assert_eq!(val.attr, Some(23.42));

        let val = from_str::<Root>(r#"<root></root>"#).unwrap();
        assert_eq!(val.attr, None);
    }

    #[test]
    fn child_variants() {
        #[derive(Debug, PartialEq, Deserialize)]
        enum Root {
            Foo(Foo),
            Bar(Bar),
        }

        #[derive(Debug, PartialEq, Deserialize)]
        struct Foo {
            attr: i64,
        }

        #[derive(Debug, PartialEq, Deserialize)]
        struct Bar {
            child: u32,
        }

        let val = from_str::<Root>(r#"<root><Foo attr="23" /></root>"#).unwrap();
        assert_eq!(val, Root::Foo(Foo { attr: 23 }));

        let val = from_str::<Root>(r#"<root><Bar><child>42</child></Bar></root>"#).unwrap();
        assert_eq!(val, Root::Bar(Bar { child: 42 }));
    }

    #[test]
    fn attribute_variants() {
        #[derive(Debug, PartialEq, Deserialize)]
        enum Root {
            Foo(u32),
            Bar(i64),
        }

        let val = from_str::<Root>(r#"<root Foo="23" />"#).unwrap();
        assert_eq!(val, Root::Foo(23));

        let val = from_str::<Root>(r#"<root Bar="42" />"#).unwrap();
        assert_eq!(val, Root::Bar(42));
    }

    #[test]
    fn borrowed_str() {
        let document = Document::parse("<root><child>foobar</child></root>").unwrap();

        #[derive(Deserialize)]
        struct Root<'a> {
            child: &'a str,
        }

        let val = from_doc::<Root>(&document).unwrap();
        assert_eq!(val.child, "foobar");
    }

    #[test]
    fn unit_struct() {
        #[derive(Deserialize)]
        #[allow(dead_code)]
        struct Root {
            child: Child,
        }

        #[derive(Deserialize)]
        struct Child;

        from_str::<Root>(r#"<root><child /></root>"#).unwrap();

        from_str::<Root>(r#"<root><child>foobar</child></root>"#).unwrap();
    }

    #[test]
    fn unit_variant() {
        #[derive(Debug, PartialEq, Deserialize)]
        enum Root {
            Child,
        }

        from_str::<Root>(r#"<root><Child /></root>"#).unwrap();

        from_str::<Root>(r#"<root><Child>foobar</Child></root>"#).unwrap();
    }
}
