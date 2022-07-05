use std::{cmp::Ordering, collections::VecDeque, fmt, fs, iter, path::PathBuf, str};

use bimap::BiMap;
use clap::{ArgEnum, Parser};
use petgraph::{graph::NodeIndex, stable_graph::StableDiGraph, Direction};
use regex::Regex;

mod ast;

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
impl NodeKind {
	fn as_conditions(&self) -> Option<(&Condition, &Condition)> {
		match self {
			Self::Conditions { left, right } => Some((left, right)),
			Self::Result(_) => None,
		}
	}
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
	let root_node_id = root.id;

	let decision_tree = DecisonTree::new(root, nodes);

	let output = |output: &str| match args.output_location {
		None => println!("{}", output),
		Some(p) => fs::write(p, output).expect("Unable to write output to file"),
	};

	match args.output_format {
		OutputFormat::GraphvizDot => {
			let s = petgraph::dot::Dot::new(&decision_tree.graph).to_string();
			output(&s);
			return;
		}
		OutputFormat::Verilog => (),
	}

	let input_identifiers = decision_tree
		.graph
		.node_weights()
		.filter_map(|n| match &n.kind {
			NodeKind::Result(_) => None,
			NodeKind::Conditions { left, right } => Some(
				[
					left.variable.identifier.clone(),
					right.variable.identifier.clone(),
				]
				.into_iter(),
			),
		})
		.flatten()
		.map(|s| ast::Identifier::new(s))
		.collect::<Vec<_>>();

	let output_identifier = ast::Identifier::new("y");

	let vth = decision_tree
		.graph
		.node_weights()
		.filter_map(|n| match &n.kind {
			NodeKind::Result(_) => None,
			NodeKind::Conditions { left, right } => {
				Some([left.comparison_operand, right.comparison_operand].into_iter())
			}
		})
		.flatten()
		.reduce(|accum, item| {
			assert!(accum.partial_cmp(&item).unwrap() == Ordering::Equal);
			accum
		})
		.unwrap()
		.to_string();

	let mut code = ast::Code {
		includes: [
			ast::Include {
				name: "constants.vams".into(),
			},
			ast::Include {
				name: "disciplines.vams".into(),
			},
		]
		.into(),
		module: ast::Module {
			name: ast::Identifier::new("Classifier"),
			inputs: input_identifiers.clone(),
			output: output_identifier.clone(),
			electrical_statement: ast::ElectricalStatement {
				identifiers: input_identifiers
					.iter()
					.cloned()
					.chain(iter::once(output_identifier))
					.collect(),
			},
			parameter_real_statements: [ast::ParameterRealStatement {
				identifier: ast::Identifier::new("vth"),
				value: vth,
			}]
			.into(),
			analog_block: ast::AnalogBlock { statement: None },
		},
	};

	let mut nodes_list: Vec<Vec<u32>> = Vec::new();

	nodes_list.push([root_node_id].into());

	for _ in 0.. {
		let mut new_node_ids = Vec::<u32>::new();
		for node_id in nodes_list.last().unwrap().clone() {
			let x = decision_tree
				.graph
				.neighbors(*decision_tree.map.get_by_right(&node_id).unwrap())
				.map(|idx| *decision_tree.map.get_by_left(&idx).unwrap());

			new_node_ids.extend(x);
		}
		if new_node_ids.len() == 0 {
			break;
		}
		nodes_list.push(new_node_ids);
	}

	let nodes_list = nodes_list;

	let root = decision_tree
		.graph
		.node_weight(*decision_tree.map.get_by_right(&nodes_list[0][0]).unwrap())
		.unwrap()
		.kind
		.as_conditions()
		.unwrap();

	code.module.analog_block.statement = Some(Box::new(ast::Statement::IfElse(ast::IfElse {
		if_condition: ast_condition_from_node_condition(root.0.clone()),
		else_condition: ast_condition_from_node_condition(root.1.clone()),
		if_then: None,
		else_then: None,
	})));

	for i in 1..nodes_list.len() {
		let nodes = nodes_list[i].clone();

		for node in nodes {
			let mut traversal_instructions = Vec::<ConditionDirection>::new();
			let mut current_node = *decision_tree.map.get_by_right(&node).unwrap();

			loop {
				let x = decision_tree
					.graph
					.neighbors_directed(current_node, Direction::Incoming)
					.collect::<Vec<_>>();

				match x.len() {
					0 => break,
					1 => {}
					_ => unreachable!(),
				}

				let previous_node = current_node;
				current_node = x[0];

				let edge_index = decision_tree
					.graph
					.find_edge(current_node, previous_node)
					.unwrap();

				let direction = *decision_tree.graph.edge_weight(edge_index).unwrap();
				traversal_instructions.push(direction);
			}

			traversal_instructions.reverse();

			let mut insertion_point = &mut code.module.analog_block.statement;

			for i in traversal_instructions {
				insertion_point = match i {
					ConditionDirection::Left => {
						&mut insertion_point
							.as_mut()
							.unwrap()
							.as_if_else_mut()
							.unwrap()
							.if_then
					}
					ConditionDirection::Right => {
						&mut insertion_point
							.as_mut()
							.unwrap()
							.as_if_else_mut()
							.unwrap()
							.else_then
					}
				};
			}

			let _ = insertion_point.insert(Box::new(ast_statement_from_node(
				decision_tree
					.graph
					.node_weight(*decision_tree.map.get_by_right(&node).unwrap())
					.unwrap()
					.clone(),
				ast::Identifier::new("y"),
			)));
		}
	}

	output(&format!("{}", code));
}

fn ast_condition_from_node_condition(condition: Condition) -> ast::Condition {
	ast::Condition {
		input_identifier: ast::Identifier::new(condition.variable.identifier),
		operator: match condition.comparison_operator {
			ComparisonOperator::LessThan => ast::ComparisonOperator::LessThan,
			ComparisonOperator::GreaterThan => ast::ComparisonOperator::GreaterThan,
			ComparisonOperator::LessThanEq => ast::ComparisonOperator::LessThanEq,
			ComparisonOperator::GreaterThanEq => ast::ComparisonOperator::GreaterThanEq,
		},
		comparison_operand: ast::Value::Identifier(ast::Identifier::new("vth")),
	}
}

fn ast_statement_from_node(node: Node, variable: ast::Identifier) -> ast::Statement {
	match node.kind {
		NodeKind::Result(o) => ast::Statement::Assignment(ast::Assignment {
			variable,
			value: ast::Value::Number(o.value.into()),
		}),
		NodeKind::Conditions { left, right } => ast::Statement::IfElse(ast::IfElse {
			if_condition: ast_condition_from_node_condition(left),
			else_condition: ast_condition_from_node_condition(right),
			if_then: None,
			else_then: None,
		}),
	}
}
