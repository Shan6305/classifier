use std::{collections::VecDeque, fmt, fs, iter, path::PathBuf, str};

use bimap::BiMap;
use clap::{ArgEnum, Parser};
use petgraph::stable_graph::StableDiGraph;
use regex::Regex;

#[derive(Debug, Clone)]
pub struct Node {
	pub id: u32,
	pub kind: NodeKind,
}

impl fmt::Display for Node {
	fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
		match &self.kind {
			NodeKind::Result(o) => write!(f, "Node {} | Output({})", self.id, o.value,),
			NodeKind::Conditions { left, right } => {
				write!(
					f,
					"Node {} | Left(if {}{}{} then node {}) | Right(if {}{}{} then node {})",
					self.id,
					left.variable.identifier,
					left.comparison_operator.as_str(),
					left.comparison_operand,
					left.target_node,
					right.variable.identifier,
					right.comparison_operator.as_str(),
					right.comparison_operand,
					right.target_node,
				)
			}
		}
	}
}

#[derive(Debug, Clone)]
pub enum NodeKind {
	Conditions { left: Condition, right: Condition },
	Result(Output),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Output {
	value: i32,
}

#[derive(Debug, Clone)]
pub struct Condition {
	pub variable: Variable,
	pub comparison_operator: ComparisonOperator,
	pub comparison_operand: f64,
	pub target_node: u32,
}

#[derive(Debug, Clone)]
pub struct Variable {
	pub identifier: String,
}

#[derive(Debug, Clone, Copy)]
pub enum ComparisonOperator {
	LessThan,
	GreaterThan,
	LessThanEq,
	GreaterThanEq,
}
impl ComparisonOperator {
	fn as_str(&self) -> &'static str {
		match self {
			Self::LessThan => "<",
			Self::GreaterThan => ">",
			Self::LessThanEq => "<=",
			Self::GreaterThanEq => ">=",
		}
	}
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
enum ConditionDirection {
	Left,
	Right,
}
impl fmt::Display for ConditionDirection {
	fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
		write!(
			f,
			"{}",
			match self {
				Self::Left => "Left",
				Self::Right => "Right",
			}
		)
	}
}

struct DecisonTree {
	graph: StableDiGraph<Node, ConditionDirection, u32>,
	map: BiMap<petgraph::graph::NodeIndex<u32>, u32>,
}
impl DecisonTree {
	fn new(root: Node, nodes: VecDeque<Node>) -> Self {
		let mut dt = Self {
			graph: StableDiGraph::new(),
			map: BiMap::new(),
		};

		for n in iter::once(root.clone()).chain(nodes.clone()) {
			let node_id = n.id;
			let node_index = dt.graph.add_node(n);

			dt.map.insert(node_index, node_id);
		}

		for n in iter::once(root).chain(nodes) {
			let (l, r) = match n.kind {
				NodeKind::Result(_) => continue,
				NodeKind::Conditions { left, right } => (left, right),
			};

			let original_node = dt.map.get_by_right(&n.id).unwrap().clone();
			let left_node = dt.map.get_by_right(&l.target_node).unwrap().clone();
			let right_node = dt.map.get_by_right(&r.target_node).unwrap().clone();

			dt.graph
				.add_edge(original_node, left_node, ConditionDirection::Left);
			dt.graph
				.add_edge(original_node, right_node, ConditionDirection::Right);
		}

		dt
	}
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, ArgEnum)]
enum OutputFormat {
	GraphvizDot,
	Verilog,
}

#[derive(Parser, Debug)]
struct Args {
	/// Path to a text file containing the decision tree in textual format.
	#[clap(short = 'd', long = "decision-tree")]
	decision_tree: PathBuf,

	/// What format the program should output its result as.
	/// Graphviz Dot can be used for purposes of tree visualization and program testing,
	/// and can be viewed online using a website such as http://viz-js.com.
	#[clap(short = 'f', long = "output-format", value_parser)]
	output_format: OutputFormat,

	/// If specified, the file that the program should write its output to.
	/// If not specified, the program will print to stdout.
	#[clap(short = 'l', long = "output-location")]
	output_location: Option<PathBuf>,
}

fn main() {
	let args = Args::parse();

	let file_data = fs::read(args.decision_tree).unwrap();

	let decision_tree_text = str::from_utf8(&file_data).unwrap();

	let lines = decision_tree_text.lines().collect::<Vec<&str>>();

	let output_line_regex =
		Regex::new(r"^(?P<node_id>\d+) class = (?P<node_output>-?\d+)$").unwrap();

	// (?x) at the beginning enables comments, and ignores all whitespace
	// Spaces are matched with ASCII hex code 0x20
	let decision_line_regex = Regex::new(
		r"(?x)
			^(?P<node_id> \d+) # match the node id

			\x20 if \x20

			(?P<var_ident_a> x\d+) # match the first variable identifier

			(?P<comparison_a> <|> =?) # match either the less than or greater than sign

			#(?P<comp_eq_a> =?) # optionally match an equals sign

			(?P<operand_a> \d+.\d+)

			\x20 then \x20 node \x20

			(?P<target_node_a> \d+)

			\x20 elseif \x20


			(?P<var_ident_b> x\d+) # match the first variable identifier

			(?P<comparison_b> <|> =?) # match either the less than or greater than sign

			#(?P<comp_eq_b> =?) # optionally match an equals sign

			(?P<operand_b> \d+.\d+)

			\x20 then \x20 node \x20

			(?P<target_node_b> \d+)

			\x20 else \x20

			-?\d+

			$
			",
	)
	.unwrap();

	let mut nodes = lines
		.into_iter()
		.map(|l| {
			if output_line_regex.is_match(l) {
				let caps = output_line_regex.captures(l).unwrap();
				Node {
					id: caps["node_id"].parse().unwrap(),
					kind: NodeKind::Result(Output {
						value: caps["node_output"].parse().unwrap(),
					}),
				}
			} else {
				let caps = decision_line_regex.captures(l).unwrap();
				Node {
					id: caps["node_id"].parse().unwrap(),
					kind: NodeKind::Conditions {
						left: Condition {
							variable: Variable {
								identifier: caps["var_ident_a"].to_string(),
							},
							comparison_operator: match &caps["comparison_a"] {
								"<" => ComparisonOperator::LessThan,
								">" => ComparisonOperator::GreaterThan,
								"<=" => ComparisonOperator::LessThanEq,
								">=" => ComparisonOperator::GreaterThanEq,
								_ => panic!(),
							},
							comparison_operand: caps["operand_a"].parse().unwrap(),
							target_node: caps["target_node_a"].parse().unwrap(),
						},
						right: Condition {
							variable: Variable {
								identifier: caps["var_ident_b"].to_string(),
							},
							comparison_operator: match &caps["comparison_b"] {
								"<" => ComparisonOperator::LessThan,
								">" => ComparisonOperator::GreaterThan,
								"<=" => ComparisonOperator::LessThanEq,
								">=" => ComparisonOperator::GreaterThanEq,
								_ => panic!(),
							},
							comparison_operand: caps["operand_b"].parse().unwrap(),
							target_node: caps["target_node_b"].parse().unwrap(),
						},
					},
				}
			}
		})
		.collect::<VecDeque<_>>();

	let root = nodes.pop_front().unwrap();

	let dt = DecisonTree::new(root, nodes);

	let output = match args.output_format {
		OutputFormat::GraphvizDot => petgraph::dot::Dot::new(&dt.graph).to_string(),
		OutputFormat::Verilog => todo!(),
	};

	match args.output_location {
		None => println!("{}", output),
		Some(p) => fs::write(p, output).expect("Unable to write output to file"),
	}
}
