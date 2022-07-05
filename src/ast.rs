use std::fmt::{self, Display};

fn sort_dedup_identifiers(idents: impl IntoIterator<Item = Identifier>) -> Vec<Identifier> {
	let mut x = idents
		.into_iter()
		.map(|i| i.to_string())
		.collect::<Vec<_>>();

	x.sort_unstable_by_key(|s| s[1..].parse::<u32>().unwrap_or(u32::MAX));
	x.dedup();
	x.into_iter().map(|s| Identifier::new(s)).collect()
}

#[derive(Debug, Clone)]
pub struct Code {
	pub includes: Vec<Include>,
	pub module: Module,
}
impl Display for Code {
	fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
		write!(
			f,
			"{}\n{}",
			self.includes
				.iter()
				.map(|i| format!("{i}\n"))
				.collect::<String>(),
			self.module,
		)
	}
}

#[derive(Debug, Clone)]
pub struct Include {
	pub name: String,
}
impl Display for Include {
	fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
		write!(f, "`include \"{}\"", self.name)
	}
}

#[derive(Debug, Clone)]
pub struct Identifier(String);
impl Identifier {
	pub fn new<T: Into<String>>(v: T) -> Self {
		Self(v.into())
	}
}
impl Display for Identifier {
	fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
		write!(f, "{}", self.0)
	}
}

#[derive(Debug, Clone)]
pub struct Module {
	pub name: Identifier,
	pub inputs: Vec<Identifier>,
	pub output: Identifier,
	pub electrical_statement: ElectricalStatement,
	pub parameter_real_statements: Vec<ParameterRealStatement>,
	pub analog_block: AnalogBlock,
}
impl Display for Module {
	fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
			write!(
				f,
				"module {} ({}output {});\n\
					\t{}\n\
					\t{}\n\
					{}\n\
				endmodule",
				self.name,
				sort_dedup_identifiers(self.inputs.clone())
					.into_iter()
					.map(|s| format!("{s}, "))
					.collect::<String>(),
				self.output,
				self.electrical_statement,
				self.parameter_real_statements
					.iter()
					.map(|s| format!("{s}\n"))
					.collect::<String>(),
				self.analog_block
			)
	}
}

#[derive(Debug, Clone)]
pub struct ElectricalStatement {
	pub identifiers: Vec<Identifier>,
}
impl Display for ElectricalStatement {
	fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
		let mut s = sort_dedup_identifiers(self.identifiers.clone())
			.into_iter()
			.map(|i| format!("{i}, "))
			.collect::<String>();

		// Need to remove trailing space and trailing comma
		let _ = s.pop();
		let _ = s.pop();

		write!(f, "electrical {s};")
	}
}

#[derive(Debug, Clone)]
pub struct ParameterRealStatement {
	pub identifier: Identifier,
	pub value: String,
}
impl Display for ParameterRealStatement {
	fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
		write!(f, "parameter real {}={};", self.identifier, self.value)
	}
}

#[derive(Debug, Clone)]
pub struct AnalogBlock {
	pub statement: Option<Box<Statement>>,
}
impl Display for AnalogBlock {
	fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
		with_indent(|indent| {
			write!(
				f,
				"{indent}analog begin\n\
				{}\n\
				{indent}end",
				self.statement.as_ref().unwrap()
			)
		})
	}
}

#[derive(Debug, Clone)]
pub enum Statement {
	IfElse(IfElse),
	Assignment(Assignment),
}
impl Statement {
	pub fn as_if_else_mut(&mut self) -> Option<&mut IfElse> {
		match self {
			Self::IfElse(x) => Some(x),
			Self::Assignment(_) => None,
		}
	}
}
impl Display for Statement {
	fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
		write!(
			f,
			"{}",
			match self {
				Self::IfElse(x) => x.to_string(),
				Self::Assignment(a) => a.to_string(),
			}
		)
	}
}

fn with_indent(f: impl FnOnce(String) -> fmt::Result) -> fmt::Result {
	use std::sync::atomic::{AtomicUsize, Ordering};
	static INDENT: AtomicUsize = AtomicUsize::new(1);

	let n = INDENT.fetch_add(1, Ordering::SeqCst);
	let s = std::iter::repeat('\t').take(n).collect();
	let x = f(s);
	let _ = INDENT.fetch_sub(1, Ordering::SeqCst);
	x
}

#[derive(Debug, Clone)]
pub struct IfElse {
	pub if_condition: Condition,
	pub if_then: Option<Box<Statement>>,
	pub else_condition: Condition,
	pub else_then: Option<Box<Statement>>,
}
impl Display for IfElse {
	fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
		with_indent(|indent| {
			write!(
				f,
				"{indent}if ({}) begin\n\
					{}\n\
				{indent}end else if ({}) begin\n\
					{}\n\
				{indent}end",
				self.if_condition,
				self.if_then.as_ref().unwrap(),
				self.else_condition,
				self.else_then.as_ref().unwrap()
			)
		})
	}
}

#[derive(Debug, Clone)]
pub struct Condition {
	pub input_identifier: Identifier,
	pub operator: ComparisonOperator,
	pub comparison_operand: Value,
}
impl Display for Condition {
	fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
		write!(
			f,
			"V({}){}{}",
			self.input_identifier, self.operator, self.comparison_operand
		)
	}
}

#[derive(Debug, Clone)]
pub enum ComparisonOperator {
	LessThan,
	GreaterThan,
	LessThanEq,
	GreaterThanEq,
}
impl Display for ComparisonOperator {
	fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
		let s = match self {
			Self::LessThan => "<",
			Self::GreaterThan => ">",
			Self::LessThanEq => "<=",
			Self::GreaterThanEq => ">=",
		};

		write!(f, "{s}")
	}
}

#[derive(Debug, Clone)]
pub struct Assignment {
	pub variable: Identifier,
	pub value: Value,
}
impl Display for Assignment {
	fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
		with_indent(|indent| write!(f, "{indent}V({})<+{};", self.variable, self.value))
	}
}

#[derive(Debug, Clone)]
pub enum Value {
	Identifier(Identifier),
	Number(f64),
}
impl Display for Value {
	fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
		write!(
			f,
			"{}",
			match self {
				Self::Identifier(i) => i.to_string(),
				Self::Number(n) => n.to_string(),
			}
		)
	}
}
