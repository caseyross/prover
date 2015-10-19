/**
 * prover.java - a simple resolution theorem prover for propositional logic
 * Casey Ross
 * CS 4365 Assignment 3 Part 1
 */

import java.io.File;
import java.io.FileNotFoundException;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Comparator;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Scanner;
import java.util.TreeMap;


public class prover {

	static List<Clause> clauses;
	static List<Integer> lastResolved, parent1, parent2;
	static boolean proofFound = false;
	static List<Clause> proof, sortedProof;
	static List<Integer> proofParent1, proofParent2, sortedParent1, sortedParent2;
	
	public static void main(String[] args) throws FileNotFoundException {

		clauses = new ArrayList<Clause>();
		lastResolved = new ArrayList<Integer>();
		parent1 = new ArrayList<Integer>();
		parent2 = new ArrayList<Integer>();
		File inFile = new File(args[0]);
		Scanner sc = new Scanner(inFile);
		int i = -1;
		while(sc.hasNextLine()) {
			String input = sc.nextLine();
			String[] literals = input.split(" ");
			Arrays.sort(literals, new AtomComparator());
			Clause c = new Clause(literals);
			if(isNewClause(c)) {
				clauses.add(c);
				i++;
				lastResolved.add(i, i);
				parent1.add(i, -1);
				parent2.add(i, -1);
			}
//			for(Clause s : clauses) System.out.println(s);
		}
		int j = i - 1;
		resolution:
		while(!proofFound && i > 0) {
//			System.out.print("Trying to resolve" + clauses.get(i) + " (i=" + i + ") with" + clauses.get(j) + " (j=" + j + ") ...\n");
			Clause c = resolve(clauses.get(i), clauses.get(j));
//			System.out.print("New clause is: " + c + "\n");
			if(!isNewClause(c)) {
				if(j > 0) j--;
				else {
					do {
						i--;
						if(i == 0) break resolution;
					}
					while(lastResolved.get(i) == 0);
					j = lastResolved.get(i) - 1;
				}
				continue;
			}
			if(c.literals.length == 0) {
				proofFound = true;
				proof = new ArrayList<Clause>();
				proof.add(new Clause(new String[0]));
				parent1.add(clauses.size(), j);
				parent2.add(clauses.size(), i);
				continue;
			}
//			System.out.print("Adding new clause: " + c + "\n");
//			for(Clause s : clauses) System.out.println(s);
//			System.out.print(clauseCount++ + "\n");
			clauses.add(c);
			lastResolved.set(i, j);
			int last = clauses.size() - 1;
			parent1.add(last, j);
			parent2.add(last, i);
			i = last;
			j = last - 1;
			lastResolved.add(i, i);
		}
		if(proofFound) {
			proofParent1 = new ArrayList<Integer>();
			proofParent2 = new ArrayList<Integer>();
			proofParent1.add(parent1.get(parent1.size() - 1));
			proofParent2.add(parent2.get(parent2.size() - 1));
			addToProof(parent1.get(parent1.size() - 1));
			addToProof(parent2.get(parent2.size() - 1));
			sortedParent1 = new ArrayList<Integer>();
			sortedParent2 = new ArrayList<Integer>();
//			for(int n = 0; n < proof.size(); n++) System.out.println(proof.get(n).toString() + " " + proofParent1.get(n) + " " + proofParent2.get(n));
			sortedProof = proofSort(proof);
			for(Clause c : sortedProof) {
				sortedParent1.add(proofParent1.get(proof.indexOf(c)));
				sortedParent2.add(proofParent2.get(proof.indexOf(c)));
			}
			proof = sortedProof;
			proofParent1 = sortedParent1;
			proofParent2 = sortedParent2;
//			for(int n = 0; n < proof.size(); n++) {
//				System.out.print("{" + sortedParent1.get(n) + " " + sortedParent2.get(n) + "} ");
//			}
			Map<Integer, Integer> numbering = new TreeMap<Integer, Integer>();
			for(int n = 0; n < proof.size(); n++) numbering.put(clauses.indexOf(proof.get(n)), n+1);
			int width = 0;
			for(Clause c : proof) if(c.toString().length() > width) width = c.toString().length();
			for(int n = 0; n < proof.size() - 1; n++) {
				System.out.printf("%-" + (width + 4) + "s", (n+1) + ".  " + proof.get(n).toString());
				if(proofParent1.get(n) == -1) System.out.print("  {}\n");
				else {
					int p1 = numbering.get(proofParent1.get(n));
					int p2 = numbering.get(proofParent2.get(n));
					System.out.print("  {" + Math.min(p1, p2) + "," + Math.max(p1, p2) + "}\n");
				}
			}
			System.out.printf("%-" + (width + 4) + "s%s", proof.size() + ".  False", "  {" + numbering.get(proofParent1.get(proof.size() - 1)) + "," + numbering.get(proofParent2.get(proof.size() - 1)) + "}\n");
		}
		else System.out.print("Failure\n");
		System.out.print("Size of final clause set:  " + (clauses.size() + 1) + "\n");

	}
	
	static List<Clause> proofSort(List<Clause> clauses) {
		
		if(clauses.size() == 1) return clauses;
		List<Clause> left = clauses.subList(0, clauses.size() / 2);
		List<Clause> right = clauses.subList(clauses.size() / 2, clauses.size());
//		System.out.println();
//		for(Clause c : left) {
//			System.out.print("[" + proofParent1.get(proof.indexOf(c)) + " " + proofParent2.get(proof.indexOf(c)) + "] ");
//		}
//		System.out.println();
//		for(Clause c : right) {
//			System.out.print("[" + proofParent1.get(proof.indexOf(c)) + " " + proofParent2.get(proof.indexOf(c)) + "] ");
//		}
		return merge(proofSort(left), proofSort(right));
		
	}
	
	static List<Clause> merge(List<Clause> a, List<Clause> b) {
		
		List<Clause> result = new ArrayList<Clause>(a.size() + b.size());
		int i = 0, j = 0, indexA = -1, indexB = -1;
		while(i < a.size() && j < b.size()) {
			indexA = proof.indexOf(a.get(i));
			indexB = proof.indexOf(b.get(j));
//			System.out.println(proofParent2.get(indexA) + " " + proofParent2.get(indexB));
			if(!(proofParent2.get(indexA) == proofParent2.get(indexB))) {
				if(proofParent2.get(indexA) < proofParent2.get(indexB)) {
//					System.out.print(" Parent2 of i < parent2 of j: ");
					result.add(a.get(i));
//					System.out.print("(" + proofParent1.get(proof.indexOf(b.get(j))) + " " + proofParent2.get(proof.indexOf(b.get(j))) + ") ");
//					System.out.print("<" + proofParent1.get(proof.indexOf(a.get(i))) + " " + proofParent2.get(proof.indexOf(a.get(i))) + "> ");
					i++;
				}
				else {
					result.add(b.get(j));
//					System.out.print(" Parent2 of i > parent2 of j: ");
//					System.out.print("(" + proofParent1.get(proof.indexOf(a.get(i))) + " " + proofParent2.get(proof.indexOf(a.get(i))) + ") ");
//					System.out.print("<" + proofParent1.get(proof.indexOf(b.get(j))) + " " + proofParent2.get(proof.indexOf(b.get(j))) + "> ");
					j++;
				}
			}
			else {
				if(proofParent1.get(indexA) < proofParent1.get(indexB)) {
//					System.out.print(" Parent1 of i < parent1 of j: ");
					result.add(a.get(i));
//					System.out.print("<" + proofParent1.get(proof.indexOf(a.get(i))) + " " + proofParent2.get(proof.indexOf(a.get(i))) + "> ");
					i++;
				}
				else {
//					System.out.print(" Parent1 of i > parent1 of j: ");
					result.add(b.get(j));
//					System.out.print("<" + proofParent1.get(proof.indexOf(b.get(j))) + " " + proofParent2.get(proof.indexOf(b.get(j))) + "> ");
					j++;
				}
			}
		}
		while(i < a.size()) {
//			System.out.print(" B empty: ");
			result.add(a.get(i));
//			System.out.print("<" + proofParent1.get(proof.indexOf(a.get(i))) + " " + proofParent2.get(proof.indexOf(a.get(i))) + "> ");
			i++;
		}
		while(j < b.size()) {
//			System.out.print(" A empty: ");
			result.add(b.get(j));
//			System.out.print("<" + proofParent1.get(proof.indexOf(b.get(j))) + " " + proofParent2.get(proof.indexOf(b.get(j))) + "> ");
			j++;
		}
//		System.out.println();
//		for(Clause c : result) {
//			System.out.print("[" + proofParent1.get(proof.indexOf(c)) + " " + proofParent2.get(proof.indexOf(c)) + "] ");
//		}
		return result;
		
	}
	
	static void addToProof(int n) {
		
		if(n == -1) return;
		Clause c = clauses.get(n);
		if(!proof.contains(c)) {
			proof.add(c);
			proofParent1.add(parent1.get(n));
			proofParent2.add(parent2.get(n));
			addToProof(parent1.get(n));
			addToProof(parent2.get(n));
		}
		
	}
	
	static boolean isNewClause(Clause c) {
		
		if(c == null) return false;
		if(c.literals.length == 0) return true;
		iteration:
		for(Clause o : clauses) {
			if(c.literals.length > o.literals.length)  {
				int x, y = 0;
				for(x = 0; x < c.literals.length; x++) {
					if(c.literals[x].equals(o.literals[y])) {
						y++;
						if(y == o.literals.length) return false;
					}
				}
			}
			else if(c.literals.length == o.literals.length) {
				for(int i = 0; i < c.literals.length; i++) if(!(c.literals[i].equals(o.literals[i]))) continue iteration;
				return false;
			}
		}
		return true;
		
	}
	
	static Clause resolve(Clause a, Clause b) {

		int complementCount = 0;
		for(Literal x : a.literals) {
			for(Literal y : b.literals) {
				if(x.resolves(y)) if(++complementCount == 2) return null;
			}
		}
		if(complementCount == 0) return null;
		return new Clause(a.literals, b.literals);
		
	}
	
	static class Clause {
		
		Literal[] literals;
		
		public Clause(String[] literals) {
			this.literals = new Literal[literals.length];
			for(int i = 0; i < literals.length; i++) {
				if(literals[i].startsWith("~")) this.literals[i] = new Literal(literals[i].substring(1), true);
				else this.literals[i] = new Literal(literals[i], false);
			}
		}
		
		public Clause(Literal[] a, Literal[] b) {
			LinkedList<Literal> newLiterals = new LinkedList<Literal>();
			int i = 0, j = 0;
			while(i < a.length && j < b.length) {
				if(a[i].compareTo(b[j]) < 0) {
					if(!newLiterals.contains(a[i])) newLiterals.add(a[i]);
					i++;
				}
				else if(a[i].compareTo(b[j]) > 0) {
					if(!newLiterals.contains(b[j])) newLiterals.add(b[j]);
					j++;
				}
				else {
					if(!newLiterals.contains(a[i])) newLiterals.add(a[i]);
					i++;
					j++;
				}
			}
			while(i < a.length) {
				if(!newLiterals.contains(a[i])) newLiterals.add(a[i]);
				i++;
			}
			while(j < b.length) {
				if(!newLiterals.contains(b[j])) newLiterals.add(b[j]);
				j++;
			}
			int k = 1;
			while(k < newLiterals.size()) {
				if(newLiterals.get(k-1).resolves(newLiterals.get(k))) {
					newLiterals.remove(k-1);
					newLiterals.remove(k-1);
				}
				else k++;
			}
			this.literals = new Literal[newLiterals.size()];
			this.literals = newLiterals.toArray(literals);
		}
		
		public boolean equals(Object o) {
			if(!(o instanceof Clause)) return false;
			if(!(literals.length == ((Clause)o).literals.length)) return false;
			for(int i = 0; i < literals.length; i++) if(!literals[i].equals(((Clause)o).literals[i])) return false;
			return true;
		}
		
		public String toString() {
			String s = "";
			for(Literal l : literals) {
				s += " ";
				if(l.isNegated) s += "~";
				s += l.name;
			}
			if(s.startsWith(" ")) s = s.substring(1);
			return s;
		}
		
	}
	
	static class Literal implements Comparable<Literal> {
		
		String name;
		boolean isNegated;
		
		public Literal(String name, boolean isNegated) {
			this.name = name;
			this.isNegated = isNegated;
		}
		
		public int compareTo(Literal o) {
//			System.out.println("Comparing... " + this.name + " " + o.name + " = " + this.name.compareTo(o.name));
			if(this.name.compareTo(o.name) != 0) return this.name.compareTo(o.name);
			if(this.isNegated != o.isNegated) {
				if(this.isNegated) return 1;
				return -1;
			}
			return 0;
		}
		
		public boolean equals(Object o) {
			if(!(o instanceof Literal)) return false;
			return this.name.equals(((Literal)o).name) && this.isNegated == ((Literal)o).isNegated;
		}
		
		public boolean resolves(Literal o) {
			return this.name.equals(o.name) && this.isNegated != o.isNegated;
		}
		
	}
	
	static class AtomComparator implements Comparator<String> {

		public int compare(String a, String b) {
			if((a.startsWith("~") && b.startsWith("~")) || !(a.startsWith("~") || b.startsWith("~"))) return a.compareTo(b);
			if(a.startsWith("~")) {
				a = a.substring(1);
				if(a.equals(b)) return 1;
				return a.compareTo(b);
			}
			b = b.substring(1);
			if(b.equals(a)) return -1;
			return a.compareTo(b);
		}
		
	}

}
