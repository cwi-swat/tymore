module typecomputations::tests::TestComputationModel

import lang::java::jdt::Java;
import lang::java::jdt::JavaADT;
import lang::java::jdt::refactorings::Java;
import lang::java::jdt::refactorings::JavaADT;
import lang::java::jdt::refactorings::JDT4Refactorings;

import IO;

public alias CompilUnit = map[str, rel[Entity, Entity]];

public void testComputations(list[loc] projects) { for(project <- projects) testComputations(project); }	

private void testComputations(loc project) {
	println("calculating facts and asts...");
	set[AstNode] compilationUnits = createAstsFromProject(project); 
	println("done...");
	for(AstNode cu <- compilationUnits) {
		println(cu@location);
		CompilUnit typeComputationModel = cu@typeComputationModel;
		println(typeComputationModel);
	}
}