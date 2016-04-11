package edu.umkc.hackathon;

import java.io.BufferedReader;
import java.io.DataInputStream;
import java.io.FileInputStream;
import java.io.InputStreamReader;
import java.math.BigDecimal;
import java.math.BigInteger;
import java.math.MathContext;
import java.math.RoundingMode;
import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.TreeMap;
import java.util.HashSet;
import java.util.Comparator;
import java.util.Iterator;
import java.util.List;
import java.util.Locale;
import java.util.Map;
import java.util.Scanner;
import java.util.Set;
import java.util.Stack;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import org.apache.commons.lang3.StringUtils;

public class EqParser {

	/**
	 * Definition of PI as a constant, can be used in equations as variable.
	 */
	public static final BigDecimal PI = new BigDecimal(
			"3.141592653589793");

	/**
	 * The {@link MathContext} to use for calculations.
	 */
	private MathContext mc = null;

	/**
	 * The original infix equation.
	 */
	private String equation = null;

	/**
	 * The cached RPN (Reverse Polish Notation) of the equation.
	 */
	private List<String> rpn = null;

	/**
	 * All defined operators with name and implementation.
	 */
	private Map<String, Operator> operators = new TreeMap<String, Operator>(String.CASE_INSENSITIVE_ORDER);

	/**
	 * All defined functions with name and implementation.
	 */
	private Map<String, Function> functions = new TreeMap<String, EqParser.Function>(String.CASE_INSENSITIVE_ORDER);

	/**
	 * All defined variables with name and value.
	 */
	private Map<String, BigDecimal> variables = new TreeMap<String, BigDecimal>(String.CASE_INSENSITIVE_ORDER);

	/**
	 * What character to use for decimal separators.
	 */
	private static final char decimalSeparator = '.';

	/**
	 * What character to use for minus sign (negative values).
	 */
	private static final char minusSign = '-';

	/**
	 * The BigDecimal representation of the left parenthesis, used for parsing
	 * varying numbers of function parameters.
	 */
	private static final BigDecimal PARAMS_START = new BigDecimal(0);

	/**
	 * The equation evaluators exception class.
	 */
	public static class EquationException extends RuntimeException {
		private static final long serialVersionUID = 1118142866870779047L;

		public EquationException(String message) {
			super(message);
		}
	}

	/**
	 * Abstract definition of a supported equation function. A function is
	 * defined by a name, the number of parameters and the actual processing
	 * implementation.
	 */
	public abstract class Function {
		/**
		 * Name of this function.
		 */
		private String name;
		/**
		 * Number of parameters expected for this function. -1
		 * denotes a variable number of parameters.
		 */
		private int numParams;

		/**
		 * Creates a new function with given name and parameter count.
		 * 
		 * @param name
		 *            The name of the function.
		 * @param numParams
		 *            The number of parameters for this function.
		 *            -1 denotes a variable number of parameters.
		 */
		public Function(String name, int numParams) {
			this.name = name.toUpperCase(Locale.ROOT);
			this.numParams = numParams;
		}

		public String getName() {
			return name;
		}

		public int getNumParams() {
			return numParams;
		}

		public boolean numParamsVaries() {
			return numParams < 0;
		}

		/**
		 * Implementation for this function.
		 * 
		 * @param parameters
		 *            Parameters will be passed by the equation evaluator as a
		 *            {@link List} of {@link BigDecimal} values.
		 * @return The function must return a new {@link BigDecimal} value as a
		 *         computing result.
		 */
		public abstract BigDecimal eval(List<BigDecimal> parameters);
	}

	/**
	 * Abstract definition of a supported operator. An operator is defined by
	 * its name (pattern), precedence and if it is left- or right associative.
	 */
	public abstract class Operator {
		/**
		 * This operators name (pattern).
		 */
		private String oper;
		/**
		 * Operators precedence.
		 */
		private int precedence;
		/**
		 * Operator is left associative.
		 */
		private boolean leftAssoc;

		/**
		 * Creates a new operator.
		 * 
		 * @param oper
		 *            The operator name (pattern).
		 * @param precedence
		 *            The operators precedence.
		 * @param leftAssoc
		 *            true if the operator is left associative,
		 *            else false.
		 */
		public Operator(String oper, int precedence, boolean leftAssoc) {
			this.oper = oper;
			this.precedence = precedence;
			this.leftAssoc = leftAssoc;
		}

		public String getOper() {
			return oper;
		}

		public int getPrecedence() {
			return precedence;
		}

		public boolean isLeftAssoc() {
			return leftAssoc;
		}

		/**
		 * Implementation for this operator.
		 * 
		 * @param v1
		 *            Operand 1.
		 * @param v2
		 *            Operand 2.
		 * @return The result of the operation.
		 */
		public abstract BigDecimal eval(BigDecimal v1, BigDecimal v2);
	}

	/**
	 * equation tokenizer that allows to iterate over a {@link String}
	 * equation token by token. Blank characters will be skipped.
	 */
	private class Tokenizer implements Iterator<String> {

		/**
		 * Actual position in equation string.
		 */
		private int pos = 0;

		/**
		 * The original input equation.
		 */
		private String input;
		/**
		 * The previous token or null if none.
		 */
		private String previousToken;

		/**
		 * Creates a new tokenizer for an equation.
		 * 
		 * @param input
		 *            The equation string.
		 */
		public Tokenizer(String input) {
			this.input = input.trim();
		}

		@Override
		public boolean hasNext() {
			return (pos < input.length());
		}

		/**
		 * Peek at the next character, without advancing the iterator.
		 * 
		 * @return The next character or character 0, if at end of string.
		 */
		private char peekNextChar() {
			if (pos < (input.length() - 1)) {
				return input.charAt(pos + 1);
			} else {
				return 0;
			}
		}

		@Override
		public String next() {
			StringBuilder token = new StringBuilder();
			if (pos >= input.length()) {
				return previousToken = null;
			}
			char ch = input.charAt(pos);
			while (Character.isWhitespace(ch) && pos < input.length()) {
				ch = input.charAt(++pos);
			}
			if (Character.isDigit(ch)) {
				while ((Character.isDigit(ch) || ch == decimalSeparator || ch == 'e' || ch == 'E'
						|| (ch == minusSign && token.length() > 0
								&& ('e' == token.charAt(token.length() - 1) || 'E' == token.charAt(token.length() - 1)))
						|| (ch == '+' && token.length() > 0 && ('e' == token.charAt(token.length() - 1)
								|| 'E' == token.charAt(token.length() - 1))))
						&& (pos < input.length())) {
					token.append(input.charAt(pos++));
					ch = pos == input.length() ? 0 : input.charAt(pos);
				}
			} else if (ch == minusSign && Character.isDigit(peekNextChar()) && ("(".equals(previousToken)
					|| ",".equals(previousToken) || previousToken == null || operators.containsKey(previousToken))) {
				token.append(minusSign);
				pos++;
				token.append(next());
			} else if (Character.isLetter(ch) || (ch == '_')) {
				while ((Character.isLetter(ch) || Character.isDigit(ch) || (ch == '_')) && (pos < input.length())) {
					token.append(input.charAt(pos++));
					ch = pos == input.length() ? 0 : input.charAt(pos);
				}
			} else if (ch == '(' || ch == ')' || ch == ',') {
				token.append(ch);
				pos++;
			} else {
				while (!Character.isLetter(ch) && !Character.isDigit(ch) && ch != '_' && !Character.isWhitespace(ch)
						&& ch != '(' && ch != ')' && ch != ',' && (pos < input.length())) {
					token.append(input.charAt(pos));
					pos++;
					ch = pos == input.length() ? 0 : input.charAt(pos);
					if (ch == minusSign) {
						break;
					}
				}
				if (!operators.containsKey(token.toString())) {
					throw new EquationException(
							"Unknown operator '" + token + "' at position " + (pos - token.length() + 1));
				}
			}
			return previousToken = token.toString();
		}

		@Override
		public void remove() {
			throw new EquationException("remove() not supported");
		}

		/**
		 * Get the actual character position in the string.
		 * 
		 * @return The actual character position.
		 */
		public int getPos() {
			return pos;
		}

	}

	/**
	 * Creates a new equation instance from an equation string with a given
	 * default match context of {@link MathContext#DECIMAL32}.
	 * 
	 * @param equation
	 *            The equation. E.g. "2.4*sin(3)/(2-4)" or
	 *            "sin(y)>0 & max(z, 3)>3"
	 */
	public EqParser(String equation) {
		this(equation, MathContext.DECIMAL32);
	}
	

	/**
	 * Creates a new equation instance from an equation string with a given
	 * default match context.
	 * 
	 * @param equation
	 *            The equation. E.g. "2.4*sin(3)/(2-4)" or
	 *            "sin(y)>0 & max(z, 3)>3"
	 * @param defaultMathContext
	 *            The {@link MathContext} to use by default.
	 */
	public EqParser(String equation, MathContext defaultMathContext) {
		this.mc = defaultMathContext;
		this.equation = equation;
		addOperator(new Operator("+", 20, true) {
			@Override
			public BigDecimal eval(BigDecimal v1, BigDecimal v2) {
				return v1.add(v2, mc);
			}
		});
		addOperator(new Operator("-", 20, true) {
			@Override
			public BigDecimal eval(BigDecimal v1, BigDecimal v2) {
				return v1.subtract(v2, mc);
			}
		});
		addOperator(new Operator("*", 30, true) {
			@Override
			public BigDecimal eval(BigDecimal v1, BigDecimal v2) {
				return v1.multiply(v2, mc);
			}
		});
		addOperator(new Operator("/", 30, true) {
			@Override
			public BigDecimal eval(BigDecimal v1, BigDecimal v2) {
				return v1.divide(v2, mc);
			}
		});
		addOperator(new Operator("%", 30, true) {
			@Override
			public BigDecimal eval(BigDecimal v1, BigDecimal v2) {
				return v1.remainder(v2, mc);
			}
		});
		addOperator(new Operator("^", 40, false) {
			@Override
			public BigDecimal eval(BigDecimal v1, BigDecimal v2) {
				
				int signOf2 = v2.signum();
				double dn1 = v1.doubleValue();
				v2 = v2.multiply(new BigDecimal(signOf2)); // n2 is now positive
				BigDecimal remainderOf2 = v2.remainder(BigDecimal.ONE);
				BigDecimal n2IntPart = v2.subtract(remainderOf2);
				BigDecimal intPow = v1.pow(n2IntPart.intValueExact(), mc);
				BigDecimal doublePow = new BigDecimal(Math.pow(dn1, remainderOf2.doubleValue()));

				BigDecimal result = intPow.multiply(doublePow, mc);
				if (signOf2 == -1) {
					result = BigDecimal.ONE.divide(result, mc.getPrecision(), RoundingMode.HALF_UP);
				}
				return result;
			}
		});
		addOperator(new Operator("&&", 4, false) {
			@Override
			public BigDecimal eval(BigDecimal v1, BigDecimal v2) {
				boolean b1 = !v1.equals(BigDecimal.ZERO);
				boolean b2 = !v2.equals(BigDecimal.ZERO);
				return b1 && b2 ? BigDecimal.ONE : BigDecimal.ZERO;
			}
		});

		addOperator(new Operator("||", 2, false) {
			@Override
			public BigDecimal eval(BigDecimal v1, BigDecimal v2) {
				boolean b1 = !v1.equals(BigDecimal.ZERO);
				boolean b2 = !v2.equals(BigDecimal.ZERO);
				return b1 || b2 ? BigDecimal.ONE : BigDecimal.ZERO;
			}
		});

		addOperator(new Operator(">", 10, false) {
			@Override
			public BigDecimal eval(BigDecimal v1, BigDecimal v2) {
				return v1.compareTo(v2) == 1 ? BigDecimal.ONE : BigDecimal.ZERO;
			}
		});

		addOperator(new Operator(">=", 10, false) {
			@Override
			public BigDecimal eval(BigDecimal v1, BigDecimal v2) {
				return v1.compareTo(v2) >= 0 ? BigDecimal.ONE : BigDecimal.ZERO;
			}
		});

		addOperator(new Operator("<", 10, false) {
			@Override
			public BigDecimal eval(BigDecimal v1, BigDecimal v2) {
				return v1.compareTo(v2) == -1 ? BigDecimal.ONE : BigDecimal.ZERO;
			}
		});

		addOperator(new Operator("<=", 10, false) {
			@Override
			public BigDecimal eval(BigDecimal v1, BigDecimal v2) {
				return v1.compareTo(v2) <= 0 ? BigDecimal.ONE : BigDecimal.ZERO;
			}
		});

		addOperator(new Operator("=", 7, false) {
			@Override
			public BigDecimal eval(BigDecimal v1, BigDecimal v2) {
				return v1.compareTo(v2) == 0 ? BigDecimal.ONE : BigDecimal.ZERO;
			}
		});
		addOperator(new Operator("==", 7, false) {
			@Override
			public BigDecimal eval(BigDecimal v1, BigDecimal v2) {
				return operators.get("=").eval(v1, v2);
			}
		});

		addOperator(new Operator("!=", 7, false) {
			@Override
			public BigDecimal eval(BigDecimal v1, BigDecimal v2) {
				return v1.compareTo(v2) != 0 ? BigDecimal.ONE : BigDecimal.ZERO;
			}
		});
		addOperator(new Operator("<>", 7, false) {
			@Override
			public BigDecimal eval(BigDecimal v1, BigDecimal v2) {
				return operators.get("!=").eval(v1, v2);
			}
		});

		addFunction(new Function("NOT", 1) {
			@Override
			public BigDecimal eval(List<BigDecimal> parameters) {
				boolean zero = parameters.get(0).compareTo(BigDecimal.ZERO) == 0;
				return zero ? BigDecimal.ONE : BigDecimal.ZERO;
			}
		});

		addFunction(new Function("IF", 3) {
			@Override
			public BigDecimal eval(List<BigDecimal> parameters) {
				boolean isTrue = !parameters.get(0).equals(BigDecimal.ZERO);
				return isTrue ? parameters.get(1) : parameters.get(2);
			}
		});

		addFunction(new Function("RANDOM", 0) {
			@Override
			public BigDecimal eval(List<BigDecimal> parameters) {
				double d = Math.random();
				return new BigDecimal(d, mc);
			}
		});
		addFunction(new Function("SIN", 1) {
			@Override
			public BigDecimal eval(List<BigDecimal> parameters) {
				double d = Math.sin(Math.toRadians(parameters.get(0).doubleValue()));
				return new BigDecimal(d, mc);
			}
		});
		addFunction(new Function("COS", 1) {
			@Override
			public BigDecimal eval(List<BigDecimal> parameters) {
				double d = Math.cos(Math.toRadians(parameters.get(0).doubleValue()));
				return new BigDecimal(d, mc);
			}
		});
		addFunction(new Function("TAN", 1) {
			@Override
			public BigDecimal eval(List<BigDecimal> parameters) {
				double d = Math.tan(Math.toRadians(parameters.get(0).doubleValue()));
				return new BigDecimal(d, mc);
			}
		});
		addFunction(new Function("ASIN", 1) { 
			@Override
			public BigDecimal eval(List<BigDecimal> parameters) {
				double d = Math.toDegrees(Math.asin(parameters.get(0).doubleValue()));
				return new BigDecimal(d, mc);
			}
		});
		addFunction(new Function("ACOS", 1) { 
			@Override
			public BigDecimal eval(List<BigDecimal> parameters) {
				double d = Math.toDegrees(Math.acos(parameters.get(0).doubleValue()));
				return new BigDecimal(d, mc);
			}
		});
		addFunction(new Function("ATAN", 1) {
			@Override
			public BigDecimal eval(List<BigDecimal> parameters) {
				double d = Math.toDegrees(Math.atan(parameters.get(0).doubleValue()));
				return new BigDecimal(d, mc);
			}
		});
		addFunction(new Function("SINH", 1) {
			@Override
			public BigDecimal eval(List<BigDecimal> parameters) {
				double d = Math.sinh(parameters.get(0).doubleValue());
				return new BigDecimal(d, mc);
			}
		});
		addFunction(new Function("COSH", 1) {
			@Override
			public BigDecimal eval(List<BigDecimal> parameters) {
				double d = Math.cosh(parameters.get(0).doubleValue());
				return new BigDecimal(d, mc);
			}
		});
		addFunction(new Function("TANH", 1) {
			@Override
			public BigDecimal eval(List<BigDecimal> parameters) {
				double d = Math.tanh(parameters.get(0).doubleValue());
				return new BigDecimal(d, mc);
			}
		});
		addFunction(new Function("RAD", 1) {
			@Override
			public BigDecimal eval(List<BigDecimal> parameters) {
				double d = Math.toRadians(parameters.get(0).doubleValue());
				return new BigDecimal(d, mc);
			}
		});
		addFunction(new Function("DEG", 1) {
			@Override
			public BigDecimal eval(List<BigDecimal> parameters) {
				double d = Math.toDegrees(parameters.get(0).doubleValue());
				return new BigDecimal(d, mc);
			}
		});
		addFunction(new Function("MAX", -1) {
			@Override
			public BigDecimal eval(List<BigDecimal> parameters) {
				if (parameters.size() == 0) {
					throw new EquationException("MAX requires at least one parameter");
				}
				BigDecimal max = null;
				for (BigDecimal parameter : parameters) {
					if (max == null || parameter.compareTo(max) > 0) {
						max = parameter;
					}
				}
				return max;
			}
		});
		addFunction(new Function("MIN", -1) {
			@Override
			public BigDecimal eval(List<BigDecimal> parameters) {
				if (parameters.size() == 0) {
					throw new EquationException("MIN requires at least one parameter");
				}
				BigDecimal min = null;
				for (BigDecimal parameter : parameters) {
					if (min == null || parameter.compareTo(min) < 0) {
						min = parameter;
					}
				}
				return min;
			}
		});
		addFunction(new Function("ABS", 1) {
			@Override
			public BigDecimal eval(List<BigDecimal> parameters) {
				return parameters.get(0).abs(mc);
			}
		});
		addFunction(new Function("LOG", 1) {
			@Override
			public BigDecimal eval(List<BigDecimal> parameters) {
				double d = Math.log(parameters.get(0).doubleValue());
				return new BigDecimal(d, mc);
			}
		});
		addFunction(new Function("LOG10", 1) {
			@Override
			public BigDecimal eval(List<BigDecimal> parameters) {
				double d = Math.log10(parameters.get(0).doubleValue());
				return new BigDecimal(d, mc);
			}
		});
		addFunction(new Function("ROUND", 2) {
			@Override
			public BigDecimal eval(List<BigDecimal> parameters) {
				BigDecimal toRound = parameters.get(0);
				int precision = parameters.get(1).intValue();
				return toRound.setScale(precision, mc.getRoundingMode());
			}
		});
		addFunction(new Function("FLOOR", 1) {
			@Override
			public BigDecimal eval(List<BigDecimal> parameters) {
				BigDecimal toRound = parameters.get(0);
				return toRound.setScale(0, RoundingMode.FLOOR);
			}
		});
		addFunction(new Function("CEILING", 1) {
			@Override
			public BigDecimal eval(List<BigDecimal> parameters) {
				BigDecimal toRound = parameters.get(0);
				return toRound.setScale(0, RoundingMode.CEILING);
			}
		});
		addFunction(new Function("SQRT", 1) {
			@Override
			public BigDecimal eval(List<BigDecimal> parameters) {
				/*
				 * From The Java Programmers Guide To numerical Computing
				 * (Ronald Mak, 2003)
				 */
				BigDecimal x = parameters.get(0);
				if (x.compareTo(BigDecimal.ZERO) == 0) {
					return new BigDecimal(0);
				}
				if (x.signum() < 0) {
					throw new EquationException("Argument to SQRT() function must not be negative");
				}
				BigInteger n = x.movePointRight(mc.getPrecision() << 1).toBigInteger();

				int bits = (n.bitLength() + 1) >> 1;
				BigInteger ix = n.shiftRight(bits);
				BigInteger ixPrev;

				do {
					ixPrev = ix;
					ix = ix.add(n.divide(ix)).shiftRight(1);
					// Give other threads a chance to work;
					Thread.yield();
				} while (ix.compareTo(ixPrev) != 0);

				return new BigDecimal(ix, mc.getPrecision());
			}
		});

		variables.put("PI", PI);
		variables.put("TRUE", BigDecimal.ONE);
		variables.put("FALSE", BigDecimal.ZERO);

	}

	/**
	 * Is the string a number?
	 * 
	 * @param st
	 *            The string.
	 * @return true, if the input string is a number.
	 */
	private boolean isNumber(String st) {
		if (st.charAt(0) == minusSign && st.length() == 1)
			return false;
		if (st.charAt(0) == '+' && st.length() == 1)
			return false;
		if (st.charAt(0) == 'e' || st.charAt(0) == 'E')
			return false;
		for (char ch : st.toCharArray()) {
			if (!Character.isDigit(ch) && ch != minusSign && ch != decimalSeparator && ch != 'e' && ch != 'E'
					&& ch != '+')
				return false;
		}
		return true;
	}

	/**
	 * Implementation of the <i>Shunting Yard</i> algorithm to transform an
	 * infix equation to a RPN equation.
	 * 
	 * @param equation
	 *            The input equation in infx.
	 * @return A RPN representation of the equation, with each token as a list
	 *         member.
	 */
	private List<String> shuntingYard(String equation) {
		List<String> outputQueue = new ArrayList<String>();
		Stack<String> stack = new Stack<String>();

		Tokenizer tokenizer = new Tokenizer(equation);

		String lastFunction = null;
		String previousToken = null;
		while (tokenizer.hasNext()) {
			String token = tokenizer.next();
			if (isNumber(token)) {
				outputQueue.add(token);
			} else if (variables.containsKey(token)) {
				outputQueue.add(token);
			} else if (functions.containsKey(token.toUpperCase(Locale.ROOT))) {
				stack.push(token);
				lastFunction = token;
			} else if (Character.isLetter(token.charAt(0))) {
				stack.push(token);
			} else if (",".equals(token)) {
				while (!stack.isEmpty() && !"(".equals(stack.peek())) {
					outputQueue.add(stack.pop());
				}
				if (stack.isEmpty()) {
					throw new EquationException("Parse error for function '" + lastFunction + "'");
				}
			} else if (operators.containsKey(token)) {
				Operator o1 = operators.get(token);
				String token2 = stack.isEmpty() ? null : stack.peek();
				while (token2 != null && operators.containsKey(token2)
						&& ((o1.isLeftAssoc() && o1.getPrecedence() <= operators.get(token2).getPrecedence())
								|| (o1.getPrecedence() < operators.get(token2).getPrecedence()))) {
					outputQueue.add(stack.pop());
					token2 = stack.isEmpty() ? null : stack.peek();
				}
				stack.push(token);
			} else if ("(".equals(token)) {
				if (previousToken != null) {
					if (isNumber(previousToken)) {
						throw new EquationException("Missing operator at character position " + tokenizer.getPos());
					}
					// if the ( is preceded by a valid function, then it
					// denotes the start of a parameter list
					if (functions.containsKey(previousToken.toUpperCase(Locale.ROOT))) {
						outputQueue.add(token);
					}
				}
				stack.push(token);
			} else if (")".equals(token)) {
				while (!stack.isEmpty() && !"(".equals(stack.peek())) {
					outputQueue.add(stack.pop());
				}
				if (stack.isEmpty()) {
					throw new RuntimeException("Mismatched parentheses");
				}
				stack.pop();
				if (!stack.isEmpty() && functions.containsKey(stack.peek().toUpperCase(Locale.ROOT))) {
					outputQueue.add(stack.pop());
				}
			}
			previousToken = token;
		}
		while (!stack.isEmpty()) {
			String element = stack.pop();
			if ("(".equals(element) || ")".equals(element)) {
				throw new RuntimeException("Mismatched parentheses");
			}
			if (!operators.containsKey(element)) {
				throw new RuntimeException("Unknown operator or function: " + element);
			}
			outputQueue.add(element);
		}
		return outputQueue;
	}

	/**
	 * Evaluates the equation.
	 * 
	 * @return The result of the equation.
	 */
	public BigDecimal eval() {

		Stack<BigDecimal> stack = new Stack<BigDecimal>();

		for (String token : getRPN()) {
			if (operators.containsKey(token)) {
				BigDecimal v1 = stack.pop();
				BigDecimal v2 = stack.pop();
				stack.push(operators.get(token).eval(v2, v1));
			} else if (variables.containsKey(token)) {
				stack.push(variables.get(token).round(mc));
			} else if (functions.containsKey(token.toUpperCase(Locale.ROOT))) {
				Function f = functions.get(token.toUpperCase(Locale.ROOT));
				ArrayList<BigDecimal> p = new ArrayList<BigDecimal>(!f.numParamsVaries() ? f.getNumParams() : 0);
				// pop parameters off the stack until we hit the start of
				// this function's parameter list
				while (!stack.isEmpty() && stack.peek() != PARAMS_START) {
					p.add(0, stack.pop());
				}
				if (stack.peek() == PARAMS_START) {
					stack.pop();
				}
				if (!f.numParamsVaries() && p.size() != f.getNumParams()) {
					throw new EquationException(
							"Function " + token + " expected " + f.getNumParams() + " parameters, got " + p.size());
				}
				BigDecimal fResult = f.eval(p);
				stack.push(fResult);
			} else if ("(".equals(token)) {
				stack.push(PARAMS_START);
			} else {
				stack.push(new BigDecimal(token, mc));
			}
		}
		return stack.pop().stripTrailingZeros();
	}

	/**
	 * Sets the precision for equation evaluation.
	 * 
	 * @param precision
	 *            The new precision.
	 * 
	 * @return The equation, allows to chain methods.
	 */
	public EqParser setPrecision(int precision) {
		this.mc = new MathContext(precision);
		return this;
	}

	/**
	 * Sets the rounding mode for equation evaluation.
	 * 
	 * @param roundingMode
	 *            The new rounding mode.
	 * @return The equation, allows to chain methods.
	 */
	public EqParser setRoundingMode(RoundingMode roundingMode) {
		this.mc = new MathContext(mc.getPrecision(), roundingMode);
		return this;
	}

	/**
	 * Adds an operator to the list of supported operators.
	 * 
	 * @param operator
	 *            The operator to add.
	 * @return The previous operator with that name, or null if
	 *         there was none.
	 */
	public Operator addOperator(Operator operator) {
		return operators.put(operator.getOper(), operator);
	}

	/**
	 * Adds a function to the list of supported functions
	 * 
	 * @param function
	 *            The function to add.
	 * @return The previous operator with that name, or null if
	 *         there was none.
	 */
	public Function addFunction(Function function) {
		return functions.put(function.getName(), function);
	}

	/**
	 * Sets a variable value.
	 * 
	 * @param variable
	 *            The variable name.
	 * @param value
	 *            The variable value.
	 * @return The equation, allows to chain methods.
	 */
	public EqParser setVariable(String variable, BigDecimal value) {
		variables.put(variable, value);
		return this;
	}

	/**
	 * Sets a variable value.
	 * 
	 * @param variable
	 *            The variable to set.
	 * @param value
	 *            The variable value.
	 * @return The equation, allows to chain methods.
	 */
	public EqParser setVariable(String variable, String value) {
		if (isNumber(value))
			variables.put(variable, new BigDecimal(value));
		else {
			equation = equation.replaceAll("(?i)\\b" + variable + "\\b", "(" + value + ")");
			rpn = null;
		}
		return this;
	}

	/**
	 * Sets a variable value.
	 * 
	 * @param variable
	 *            The variable to set.
	 * @param value
	 *            The variable value.
	 * @return The equation, allows to chain methods.
	 */
	public EqParser with(String variable, BigDecimal value) {
		return setVariable(variable, value);
	}

	/**
	 * Sets a variable value.
	 * 
	 * @param variable
	 *            The variable to set.
	 * @param value
	 *            The variable value.
	 * @return The equation, allows to chain methods.
	 */
	public EqParser and(String variable, String value) {
		return setVariable(variable, value);
	}

	/**
	 * Sets a variable value.
	 * 
	 * @param variable
	 *            The variable to set.
	 * @param value
	 *            The variable value.
	 * @return The equation, allows to chain methods.
	 */
	public EqParser and(String variable, BigDecimal value) {
		return setVariable(variable, value);
	}

	/**
	 * Sets a variable value.
	 * 
	 * @param variable
	 *            The variable to set.
	 * @param value
	 *            The variable value.
	 * @return The equation, allows to chain methods.
	 */
	public EqParser with(String variable, String value) {
		return setVariable(variable, value);
	}

	/**
	 * Get an iterator for this equation, allows iterating over an equation
	 * token by token.
	 * 
	 * @return A new iterator instance for this equation.
	 */
	public Iterator<String> getEquationTokenizer() {
		return new Tokenizer(this.equation);
	}

	/**
	 * Cached access to the RPN notation of this equation, ensures only one
	 * calculation of the RPN per equation instance. If no cached instance
	 * exists, a new one will be created and put to the cache.
	 * 
	 * @return The cached RPN instance.
	 */
	private List<String> getRPN() {
		if (rpn == null) {
			rpn = shuntingYard(this.equation);
			validate(rpn);
		}
		return rpn;
	}

	/**
	 * Check that the equation have enough numbers and variables to fit the
	 * requirements of the operators and functions, also check for only 1 result
	 * stored at the end of the evaluation.
	 *
	 */
	private void validate(List<String> rpn) {
		
		int counter = 0;
		Stack<Integer> params = new Stack<Integer>();
		for (String token : rpn) {
			if ("(".equals(token)) {
				// is this a nested function call?
				if (!params.isEmpty()) {
					// increment the current function's param count
					// (the return of the nested function call
					// will be a parameter for the current function)
					params.set(params.size() - 1, params.peek() + 1);
				}
				// start a new parameter count
				params.push(0);
			} else if (!params.isEmpty()) {
				if (functions.containsKey(token.toUpperCase(Locale.ROOT))) {
					// remove the parameters and the ( from the counter
					counter -= params.pop() + 1;
				} else {
					// increment the current function's param count
					params.set(params.size() - 1, params.peek() + 1);
				}
			} else if (operators.containsKey(token)) {
				// we only have binary operators
				counter -= 2;
			}
			if (counter < 0) {
				throw new EquationException("Too many operators or functions at: " + token);
			}
			counter++;
		}
		if (counter > 1) {
			throw new EquationException("Too many numbers or variables");
		} else if (counter < 1) {
			throw new EquationException("Empty equation");
		}
	}

	/**
	 * Get a string representation of the RPN (Reverse Polish Notation) for this
	 * equation.
	 * 
	 * @return A string with the RPN representation for this equation.
	 */
	public String toRPN() {
		StringBuilder result = new StringBuilder();
		for (String st : getRPN()) {
			if (result.length() != 0)
				result.append(" ");
			result.append(st);
		}
		return result.toString();
	}

	/**
	 * Exposing declared variables in the equation.
	 * 
	 * @return All declared variables.
	 */
	public Set<String> getDeclaredVariables() {
		return Collections.unmodifiableSet(variables.keySet());
	}

	/**
	 * Exposing declared operators in the equation.
	 * 
	 * @return All declared operators.
	 */
	public Set<String> getDeclaredOperators() {
		return Collections.unmodifiableSet(operators.keySet());
	}

	/**
	 * Exposing declared functions.
	 * 
	 * @return All declared functions.
	 */
	public Set<String> getDeclaredFunctions() {
		return Collections.unmodifiableSet(functions.keySet());
	}

	public String parseEq(String eq, Map<String, String> varValMap) {
		
		if(varValMap.isEmpty()) {
		List<String> varList = null; 
		List<String> valList = null;
		Map<String, String> valMap = null;
		Map<String, String> sortedValMap = null;
		String temp="";
		Scanner input = new Scanner(System.in);
		Set<String> varSet = null;
		Set<String> valSet = null;
		String expression = eq;
	    if (expression!=null)
	    {

	        //list that will contain encountered words,numbers, and white space
	        varList = new ArrayList<String>();
	        valList = new ArrayList<String>();
	        valSet = new HashSet<String>();
	        valMap = new HashMap<String, String>();
	        sortedValMap = new HashMap<String, String>();

	        Pattern p = Pattern.compile("[A-Za-z]+[0-9]+_[A-Za-z]+[0-9]+|[A-Za-z]+[0-9]+_[A-Za-z]+|[A-Za-z]+[0-9]+|[A-Za-z]+");
	        Matcher m = p.matcher(expression);
	        

	        //while matches are found 
	        while (m.find())
	        {
	        	varList.add(m.group());
	        }//end while 

	        varSet = new HashSet<String>(varList);
	        Iterator<String> itr = varSet.iterator();
	        String ip;
		    while (itr.hasNext()) {
		    	temp = itr.next();
		    	System.out.println("Enter value for " + temp + ": ");
		    	ip = input.next();
	        	valMap.put(temp, ip);	
	        	valList.add(ip);
		    }
	        
	    }
	    
	    sortedValMap = new TreeMap<String, String>(
	    		new Comparator<String> () {
	    			@Override
	    	        public int compare(String s1, String s2) {
	    	            if (s1.length() > s2.length()) {
	    	                return -1;
	    	            } else if (s1.length() < s2.length()) {
	    	                return 1;
	    	            } else {
	    	                return s1.compareTo(s2);
	    	            }
	    	        }
	    		});
	    sortedValMap.putAll(valMap);
	    
	    String exp1 = "";
	    Iterator iter2 = sortedValMap.entrySet().iterator();
	    while (iter2.hasNext()) {
	    	Map.Entry pair = (Map.Entry)iter2.next();
	    	valSet.add(pair.getValue().toString());
//	        System.out.println(pair.getKey() + " --- " + pair.getValue());
	        exp1 = expression.replace(pair.getKey().toString(),  pair.getValue().toString());
	        expression = exp1;
	        exp1 = "";
	    }
	    System.out.println("Final Expression: " + expression);
//	    String exp = StringUtils.replaceEach(expression, varSet.toArray(new String[varSet.size()]), valList.toArray(new String[valList.size()]));
//	    System.out.println("Final String: " + exp);

	    return expression;
		}
		else {
			Map<String, String> sortedValMap = null;
			sortedValMap = new HashMap<String, String>();
			List<String> varList = null; 
			List<String> valList = null;
			Set<String> varSet = null;
			Set<String> valSet = null;
			valSet = new HashSet<String>();
			String expression = eq;
			
			sortedValMap = new TreeMap<String, String>(
		    		new Comparator<String> () {
		    			@Override
		    	        public int compare(String s1, String s2) {
		    	            if (s1.length() > s2.length()) {
		    	                return -1;
		    	            } else if (s1.length() < s2.length()) {
		    	                return 1;
		    	            } else {
		    	                return s1.compareTo(s2);
		    	            }
		    	        }
		    		});
		    sortedValMap.putAll(varValMap);
		    
		    String exp1 = "";
		    varSet = sortedValMap.keySet();
		    valList = new ArrayList(sortedValMap.values());
		    Iterator iter2 = sortedValMap.entrySet().iterator();
		    while (iter2.hasNext()) {
		    	Map.Entry pair = (Map.Entry)iter2.next();
		    	valSet.add(pair.getValue().toString());
//		        System.out.println(pair.getKey() + " --- " + pair.getValue());
		        exp1 = expression.replace(pair.getKey().toString(),  pair.getValue().toString());
		        expression = exp1;
		        exp1 = "";
		    }
		    System.out.println("Final Expression: " + expression);
//		    String exp = StringUtils.replaceEach(expression, varSet.toArray(new String[varSet.size()]), valList.toArray(new String[valList.size()]));
//		    System.out.println("Final String: " + exp);

		    return expression;
		    
		}
		
	}
	public static void main(String args[]) {
		String err = "";
		String filePath = "", varFilePath="";
		int choice = 0, ch=0;
		String eq = "", parsedEq="";
		String line;
        int result;
        Set<String> vList = null;
        Map<String, String> varValMap = null;
        varValMap = new HashMap<String, String>();
        int lineNumber = 1;
		Scanner in = new Scanner(System.in);
		while(choice != 1 && choice != 2 && choice != 3) {
		System.out.println("Select mode: \n 1. Single equation evaluation\n "
				+ "2. Bulk evaluation of equations by uploading a file\n "
				+ "3. Exit\n Enter your choice: ");
		choice = in.nextInt();
		if(choice !=1 && choice != 2 && choice != 3) {
			System.out.println("Invalid input. Try again....\n");
		}
		}
		if(choice == 1) {
			System.out.println(" Enter the equation: ");
			BufferedReader br = new BufferedReader(new InputStreamReader(System.in));
			try {
				eq = br.readLine();	
			} catch(Exception e) {
				System.out.println("Input read error");
			}
			
			try {
				EqParser equation1 = new EqParser(eq);
				parsedEq = equation1.parseEq(eq, varValMap);
				EqParser equation2 = new EqParser(parsedEq);
				result = equation2.eval().toBigInteger().intValue();
				if(result == 1) {
					System.out.println("Equation " + eq + " is true");
				}
				else {
					System.out.println("Equation " + eq + " is false");
				}

			} catch (EquationException e) {
				System.out.println("Exception....");
				err = e.getMessage();
				System.out.println(err);
			}
		}
		else if (choice == 2) {
		
		 System.out.println("Enter the file path: ");
		 filePath = in.next();
		 System.out.println("File Path is: " + filePath);
		 while(ch != 1 && ch != 2 && ch != 3) {
		 System.out.println("Do you want to upload the variables list?\n"
		 		+ "  1. Yes\n"
		 		+ "  2. No\n Enter your choice: ");
		 		ch = in.nextInt();
		 if(ch == 1) {
			 System.out.println("Please provide the csv file path (variable,value)");
			varFilePath = in.next();
		 }
		 else if(ch ==2) {
			 continue;
		 }
		 else {
			 System.out.println("Wrong input. Please try again...");
		 }
		 }
		 
		 try{
			    FileInputStream fstream = new FileInputStream(varFilePath);
			    // Get the object of DataInputStream
			    DataInputStream din = new DataInputStream(fstream);
			    BufferedReader br = new BufferedReader(new InputStreamReader(din));
			    varValMap = new HashMap<String, String>();
			        while ((line = br.readLine()) != null) {
		           try {
		        	   String str[] = line.split(",");
		              
		                   
		                   varValMap.put(str[0], str[1]);
		               
						
					} catch (EquationException e) {
						System.out.println("Exception while parsing the variables list....");
						err = e.getMessage();
						System.out.println(err);
					}
		 }
			      br.close();  
			    } catch(Exception e) {
			    	System.out.println(e.toString());
			    }
		 
		 try{
			    FileInputStream fstream = new FileInputStream(filePath);
			    // Get the object of DataInputStream
			    DataInputStream din = new DataInputStream(fstream);
			    BufferedReader br = new BufferedReader(new InputStreamReader(din));
			        
			        while ((line = br.readLine()) != null) {
		           try {
		        	    EqParser equation3 = new EqParser(line);
						parsedEq = equation3.parseEq(line, varValMap);
						EqParser equation4 = new EqParser(parsedEq);
						result = equation4.eval().toBigInteger().intValue();
						
						if(result == 1) {
							System.out.println("Line: " + lineNumber + " Equation " + line + " is true");
						}
						else {
							System.out.println("Line: " + lineNumber + " Equation " + line + " is false");
						}
//						System.out.println("Line Number: " + lineNumber + " Value: " + equation.eval());
						lineNumber++;
					} catch (EquationException e) {
						System.out.println("Exception....");
						err = e.getMessage();
						System.out.println(err);
					}
		 }
			      br.close();  
			    } catch(Exception e) {
			    	System.out.println(e.toString());
			    }
		
		}
		else if( choice == 3) {
			System.exit(0);
		}
		in.close();
	}

}
