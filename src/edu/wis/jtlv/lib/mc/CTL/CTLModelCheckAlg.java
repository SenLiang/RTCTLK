package edu.wis.jtlv.lib.mc.CTL;

import java.util.Vector;

import edu.wis.jtlv.env.module.*;
import edu.wis.jtlv.env.spec.*;
import edu.wis.jtlv.lib.*;
import edu.wis.jtlv.old_lib.mc.ModelCheckException;
import net.sf.javabdd.BDD;
import edu.wis.jtlv.env.Env;
import edu.wis.jtlv.lib.mc.ModelCheckAlgException;
import edu.wis.jtlv.lib.mc.ModelCheckAlgI;

import static edu.wis.jtlv.env.spec.Operator.*;

/**
 * <p>
 * An implementation for CTL model checking.
 * </p>
 * 
 * <p>
 * checking CTL with fairness based on Li-On's algorithm. These have been
 * checked (with TLV) on the dining philosophers problem for various number of
 * philosophers (up to 9).
 * </p>
 * <p>
 * Fairness:<br>
 * ce_fair_g(p): handles both justice and compassion using Lions algorithm<br>
 * 
 * EfX(p), EfU(,q), EfG(p), EfF(p), AfX(p), AfU(p,q), AfG(p), AfF(p) ( justice
 * only )<br>
 * 
 * agptoafq(p,q): states satisfying AG(p --> AF q) over fair paths
 * </p>
 * 
 * @version {@value edu.wis.jtlv.env.Env#version}
 * @author yaniv sa'ar.
 * 
 */
public class CTLModelCheckAlg extends ModelCheckAlgI {
	private Spec property;
	public Spec getProperty() {
		return property;
	}

	//add
	Module design = getDesign();
	BDD feas = design.feasible();//所有的可达状态

	public void setProperty(Spec property) {
		this.property = property;
	}

	private BDD FairStates = null;

	public BDD getReachableStates() {
		if(this.ReachableStates == null)
			this.ReachableStates = this.getDesign().reachable();
		return ReachableStates;
	}

	public void setReachableStates(BDD reachableStates) {
		ReachableStates = reachableStates;
	}

	private BDD ReachableStates = null;

	public CTLModelCheckAlg(ModuleWithStrongFairness design, Spec property) {
		super(design);
		if (property == null)
			throw new RuntimeException("Cannot model check a null"
					+ " specification.");
		this.property = property;
		this.FairStates = null;
	}

	/* (non-Javadoc)
	 * @see edu.wis.jtlv.lib.mc.ModelCheckAlgI#getDesign()
	 */
	protected ModuleWithStrongFairness getDesign() {
		return (ModuleWithStrongFairness) super.getDesign();
	}

	/**
	 * <p>
	 * Check that the property is a CTL property.
	 * </p>
	 * 
	 * @throws AlgExceptionI
	 *             If The specification is not a CTL specification.
	 * 
	 * @return Nothing.
	 * 
	 * @see edu.wis.jtlv.lib.AlgI#preAlgorithm()
	 */
	@Override
	public AlgResultI preAlgorithm() throws AlgExceptionI {

		if (!(property.isCTLSpec()|property.isRealTimeCTLSpec())) // Real Time CTL is not included here.
			throw new ModelCheckAlgException("Cannot model check non CTL"
					+ " specification: " + property);
		return null;
	}

	/**
	 * <p>
	 * Given a specification \phi (as a formula in temporal logic) we want to
	 * decide whether \phi is valid over finite state program P , i.e. whether
	 * all the computations of the design satisfy \phi.
	 * </p>
	 * 
	 * @throws ModelCheckAlgException
	 *             When cannot identify one of the operators.
	 * 
	 * @return a string result with "VALID", or "NOT VALID" (i.e.
	 *         {@link edu.wis.jtlv.lib.AlgResultString}).
	 * 
	 * @see edu.wis.jtlv.lib.AlgI#postAlgorithm()
	 */
	@Override
	public AlgResultI doAlgorithm() throws AlgExceptionI {
		System.out.println("model checking: " + property);
		//setFairStates(Env.TRUE());

		// could throw an exception...
		BDD calculateStates = satCTL(property);
		BDD FairInitStates = getDesign().initial().and(getFairStates());
//		if (!getDesign().initial().imp(calculateStates).not().isZero()) {
		if(FairInitStates.imp(calculateStates).isOne()){
			return new AlgResultString(true, "*** Property is VALID ***");
		}else{
			BDD[] example = new BDD[0];
			try {
				example = extractWithness(property);
			} catch (ModelCheckException e) {
				e.printStackTrace();
			}
			if (example==null)
				return new AlgResultString(false, "*** Property is NOT VALID ***");
			else
				return new AlgResultPath(false, example);
		}
	}

	/**
	 * <p>
	 * Does nothing.
	 * </p>
	 * 
	 * @throws AlgExceptionI
	 *             Never.
	 * 
	 * @return Nothing.
	 * 
	 * @see edu.wis.jtlv.lib.AlgI#postAlgorithm()
	 */
	@Override
	public AlgResultI postAlgorithm() throws AlgExceptionI {
		return null;
	}

	public BDD satCTL(Spec property) throws ModelCheckAlgException {
		if (property instanceof SpecBDD)
			return ((SpecBDD) property).getVal();
		// else it is SpecExp since this cannot be a Real Time CTL.
		// and it also cannot be a triplet operator.
		SpecExp propExp = (SpecExp) property;
		Operator op = propExp.getOperator();
		Spec[] child = propExp.getChildren();
		//	BDD left = CTLAux(child[0]);
		//  BDD right = (op.isBinary()) ? CTLAux(child[1]) : null;

		int noo = op.numOfOperands();
		SpecRange range = null;
		BDD left=null;
		BDD right=null;

		if (noo==1) //EX, EF, EG, AX, AF,AG left
			left=satCTL(child[0]);
		if (noo==2) {//ABF, ABG, EBF, EBG  left or right
			if (child[0] instanceof SpecRange)
			{   range = (SpecRange) child[0];
				left= satCTL(child[1]);}//xxxxxxxx
			else
			{   left=satCTL(child[0]);//AU GU
				right=satCTL(child[1]);
			}
		}
		if (noo==3)// ABU, EBU
		{
			if (child[1] instanceof SpecRange)
			{ range = (SpecRange) child[1];
				left=satCTL(child[0]);//xxxxxxxx
				right=satCTL(child[2]);//xxxxxxxxx
			}
		}
		// propositional
		if (op == Operator.NOT)
			return left.not();
		if (op == Operator.AND)
			return left.and(right);
		if (op == Operator.OR)
			return left.or(right);
		if (op == Operator.XOR)
			return left.xor(right);
		if (op == Operator.XNOR)
			return left.xor(right).not();
		if (op == Operator.IFF)
			return left.biimp(right);
		if (op == Operator.IMPLIES)
			return left.imp(right);

		// temporal
		if (op == Operator.EX)
			return EfX(left);
		if (op == Operator.AX)
			return AfX(left);
		if (op == Operator.EF)
			return EfF(left);
		if (op == Operator.AF)
			return AfF(left);
		if (op == Operator.EG)
			return EfG(left);
		if (op == Operator.AG)
			return AfG(left);
		if (op == Operator.AU)
			return AfU(left, right);
		if (op == Operator.EU)
			return EfU(left, right);
		//Uppdate by LS on : 2017/10/20
		// bounded CTL temporal
		if (op == Operator.EBU)
			return EfBU(range.getFrom(), range.getTo(), left, right);//EfBU(int from, int to, BDD p, BDD q)
		if (op == Operator.ABU)//AfBU(int from, int to, BDD p, BDD q)
			return AfBU(range.getFrom(), range.getTo(), left, right);
		if (op == Operator.EBF)//EfBF(int from, int to, BDD p)
			return EfBF(range.getFrom(), range.getTo(), left);
		if (op == Operator.ABF)//(int from, int to, BDD p)
			return AfBF(range.getFrom(), range.getTo(), left);
		if (op == Operator.EBG)//(int from, int to, BDD p)
			return EfBG(range.getFrom(), range.getTo(), left);
		if (op == Operator.ABG)//AfBG(int from, int to, BDD p)
			return AfBG(range.getFrom(), range.getTo(), left);

		// something is wrong.
		throw new ModelCheckAlgException(
				"Cannot identify root operator for sub" + " specification: "
						+ property);
	}

	public BDD AfX(BDD p) {
		return EfX(p.not()).not();
	}  	// AX p = !EX(!p)

	public BDD AfF(BDD p) {
		return EfG(p.not()).not();
	}	// AF p = !EG !p

	public BDD AfG(BDD p) {
		return EfF(p.not()).not();
	}	// AG p = !EF !p

	public BDD AfU(BDD p, BDD q) {	// AU(p,q) = !EU(!q, !p & !q) & !EG !q
		return EfU(q.id().not(), p.id().not().and(q.id().not())).not().and(
				EfG(q.id().not()).not());
	}

	public BDD EfX(BDD p) {
//		if (this.FairStates == null)
//			FairStates = ce_fair_g(Env.TRUE());
		return getDesign().pred(p.and(getFairStates()));
	}

	public BDD EfF(BDD p) {
		return EfU(Env.TRUE(), p);
	}

	public BDD EfG(BDD p) {
		/*
		 * Dealing with FAIRNESS
		 * 
		 * Standard model-checking function ce_fair_gj(p) for check \E_fair\G p
		 * using only justice.
		 */
		ModuleWithStrongFairness design = getDesign();
		BDD old_z, z = Env.TRUE();
		for (FixPoint<BDD> ires = new FixPoint<BDD>(); ires.advance(z);) {
			old_z = z.id();
			z = p.id();
			for (int i = design.justiceNum() - 1; i >= 0; i--) {
				BDD oldAndJust = design.justiceAt(i).and(old_z);
				z = z.id().and(design.pred(allPredsIn(p, oldAndJust)));
			}
		}
		return z;
	}

	public BDD EfU(BDD p, BDD q) {
//		if (this.FairStates == null)
//			FairStates = ce_fair_g(Env.TRUE());
		return allPredsIn(p, q.id().and(getFairStates()));
	}
	public BDD EfBU(int from, int to, BDD f, BDD g) {//****************
		BDD Z=getDesign().feasible().and(g),oldZ=null;
		for (int i=to-1;i>=from;i--){
			oldZ=Z;
			Z=f.and(getDesign().pred(Z));
			if (Z.equals(oldZ)) break;}

		for (int i=from-1;i>=0;i--){
			oldZ=Z;
			Z=f.and(getDesign().pred(Z));
			if (Z.equals(oldZ)) break;}
		return Z;
	}

	public BDD EfBG(int from, int to, BDD f) {//****************
		BDD Z=getDesign().feasible().and(f),oldZ=null;
		for (int i=to-1;i>=from;i--){
		oldZ=Z;
		Z=f.and(getDesign().pred(Z));
		if (Z.equals(oldZ)) break;}

		for (int i=from-1;i>=0;i--){
			oldZ=Z;
			Z=f.and(getDesign().pred(Z));
			if (Z.equals(oldZ)) break;}
		return Z;
	}
	// A[p BU from..to q] under fairness
	public BDD AfBU(int from, int to, BDD p, BDD q) {
		if(from==0 & to==0)
			return q.id();
		if(from>0)//(Operator.AND, new Spec[]{leftBaseSpec, new SpecExp(Operator.NEXT,transBUToLTLSPec(leftBaseSpec, baseSpec, a - 1, b))});
			return p.id().and(AfX(EfBU(from-1, to-1, p, q)));
		if(to>0)
			return q.id().or(p.id().and(AfX(EfBU(from, to-1, p, q))));
		return null;

	}
	/**A[p BU f..t q] is equivalent to
	 ! ((EBF 0..(f - 1) !p)
	 | EBG f..f ((EBG 0..(t - f) !q)
	 | E[!q BU 0..(t - f) (!q & !p)]))
	 **/
	// EBF from..to p under fairness
	public BDD EfBF(int from, int to, BDD p) {//rrrrrrrrr
		return EfBU(from, to, Env.TRUE(), p);
	}
	// ABF from..to p under fairness
	public BDD AfBF(int from, int to, BDD p) {//rrrrrrrrr
		return EfBG(from,to,p.not()).not();
	}
	// ABG from..to p under fairness
	public BDD AfBG(int from, int to, BDD p) {//rrrrrrrrr
		return EfBF(from,to,p.not()).not();
	}
	public BDD allPredsIn(BDD p, BDD q) {
		Module design = getDesign();
		for (FixPoint<BDD> ires = new FixPoint<BDD>(); ires.advance(q);)
			q = q.id().or(p.and(design.pred(q.id())));
		return q;
	}

	public void setFairStates(BDD fairStates) {
		this.FairStates = fairStates;
	}

	// Fair states will be recalculated if it currently is null
	public BDD getFairStates() {
		if(this.FairStates == null)
			this.FairStates = ce_fair_g(Env.TRUE());
		return this.FairStates;
	}

	public static boolean printable = false;

	/**
	 * <p>
	 * Li-on's ce_lfair_g package <br>
	 * Compute all accessible states satisfying e_fair_g p
	 * </p>
	 * Handles both justice and compassion using Lions algorithm.
	 * 
	 * @param p
	 * @return
	 */
	public BDD ce_fair_g(BDD p) {
		// some kind of variant to feasible algorithm.
		ModuleWithStrongFairness design = getDesign();
		// saving the previous restriction state.
		Vector<BDD> trans_restriction = design.getAllTransRestrictions();
		BDD res = design.allSucc(design.initial()).and(p);  // Line 2

		// Line 3
		design.restrictTrans(res.id().and(Env.prime(res.id())));

		for (FixPoint<BDD> ires = new FixPoint<BDD>(); ires.advance(res);) {
			// I'm doing reverse so it will be completely identical to the
			// original TLV implementation.
			for (int i = design.justiceNum() - 1; i >= 0; i--) {
				res = res.id().and(design.justiceAt(i));
				res = design.allPred(res.id()).and(design.allSucc(res.id())); // res is the set of states in the SCC, in which each circle path must past Justice i
				if (printable)
					System.out.println("justice No. " + i);
				design.restrictTrans(res.id().and(Env.prime(res.id())));
			}
			for (int i = design.compassionNum() - 1; i >= 0; i--) {
				BDD tmp = res.id().and(design.qCompassionAt(i));
				tmp = design.allPred(tmp.id()).and(design.allSucc(tmp.id()));
				res = tmp.or(res.id().and(design.pCompassionAt(i).not()));
				if (printable)
					System.out.println("compassion No. " + i);
				design.restrictTrans(res.id().and(Env.prime(res.id())));
			}

			design.removeAllTransRestrictions();
			BDD resPreds = design.pred(res.id());
			BDD resSuccs = design.succ(res.id());
			res = res.id().and(resSuccs).and(resPreds);
			design.restrictTrans(res.id().and(Env.prime(res.id())));
		}
		design.removeAllTransRestrictions();

		// returning to the previous restriction state.
		design.setAllTransRestrictions(trans_restriction);
		return this.allPredsIn(p.id(), res.id());
	}
	/*
	begin example
	 */
	private BDD[] extractWithness(Spec property) throws ModelCheckException, ModelCheckAlgException {
		//System.out.println("Spec  "+property+"initial  "+property);
		SpecExp propExp = (SpecExp) property;
		Operator op = propExp.getOperator();
		if(op==EX|op==EF|op==EG|op==EU|op==EBF|op==EBG|op==EBU) return null;
		Spec[] child = propExp.getChildren();
		int noo = op.numOfOperands();
		SpecRange range = null;
		BDD left=null;
		BDD right=null;
		if (noo==1) //EX, EF, EG, AX, AF,AG left
			left=satCTL(child[0]);
		if (noo==2) {//ABF, ABG, EBF, EBG  left or right
			if (child[0] instanceof SpecRange)
			{ range = (SpecRange) child[0];
				left=satCTL(child[1]);}//xxxxxxxx
			else
			{   left=satCTL(child[0]);//AU GU
				right=satCTL(child[1]);
			}
		}
		if (noo==3)// ABU, EBU
		{
			if (child[1] instanceof SpecRange)
			{ range = (SpecRange) child[1];
				left=satCTL(child[0]);
				right=satCTL(child[2]);
			}
		}
		//设置initial()为起点
		BDD s=design.initial().and(design.feasible().satOne(design.moduleUnprimeVars(),false));
		switch (op) {
			/** Except for NOT、FINALLY、GLOBALLY、HISTORICALLY、NEXT、NOT_PREV_NOT、ONCE、PREV、B_FINALLY、B_GLOBALLY
			 AND、OR、XOR、XNOR、IFF、IMPLIES、RELEASES、SINCE、TRIGGERED、UNTIL、B_UNTIL、B_UNTIL0 **/
			case AX:
				return EX_example(s, left.not());
			case AG:
				return EU_example(s,Env.TRUE(),left.not());
			case AF:
				return EG_example(s,left.not());
			case AU:
				BDD[] EU= EU_example(s,right.not(),left.not().and(right.not()));
				if (EU==null){
					BDD[] EG= EG_example(s,right.not());
					return EG;}
				return EU;
			case ABF:
				return EBG_example(s,range.getFrom(), range.getTo(),left.not());
			case ABG:
				return EBU_example(s,range.getFrom(), range.getTo(),Env.TRUE(),left.not());
			case ABU:
				BDD[] EBU= EBU_example(s,range.getFrom(), range.getTo(),right.not(),left.not().and(right.not()));
				if (EBU==null){
					BDD[] EBG= EBG_example(s,range.getFrom(), range.getTo(),right.not());
				    return EBG;}
				return EBU;
//				System.out.println("EBG-----------------------------------------------------------");
//				for(int i=0;i<EBG.length  ;i++)
//				{  if(EBG[i]==null)break;
//					System.out.println(i+"---"+EBG[i]);
//				}
//				System.out.println("EBU-----------------------------------------------------------");
//				for(int i=0;i<EBU.length  ;i++)
//				{  if(EBU[i]==null)break;
//					System.out.println(i+"---"+EBU[i]);
//				}
		}
		return null;
	}
	public BDD[] EX_example(BDD s, BDD f) {
		BDD next=getDesign().succ(s).and(getDesign().feasible()).satOne(design.moduleUnprimeVars(),false);
		/*
		方法2
		 */
//		if (this.ctlFair == null)
//		{
//			ctlFair = ce_fair_g(Env.TRUE());
//			acc=acc.and(ctlFair);
//		}
// next=acc.and(getDesign().reachable()).and(next);//满足f的后继状态
		BDD[] returned_path = new BDD[2];
		returned_path = new BDD[20];
		returned_path[0]=s;
		returned_path[1]=next;
		return   returned_path;
	}
	public BDD[] EU_example(BDD s,BDD f,BDD g) {
		BDD[] Z=new BDD[100];
		Z[0]=g.id().and(getDesign().feasible());
		if (Z[0].equals(Env.FALSE())) return null;
		int i=0,n=0;
		BDD[] returned_path = new BDD[100];
		while (true)
		{
			if(!s.and(Z[i]).equals(Env.FALSE()))
			{	returned_path[0]=s;
				if(!s.and(Z[0]).equals(Env.FALSE()))
				{   returned_path[0]=returned_path[0].and(Z[0]).satOne(getDesign().moduleUnprimeVars(),false);
					return returned_path;
				}
				else
				{n=i;break;}
			}
			Z[i+1]=f.and(getDesign().pred(Z[i]));
			i=i+1;
		}
		for(i=1;i<=n;i++)
			returned_path[i]=getDesign().succ(returned_path[i-1]).and(Z[n-i]).satOne(getDesign().moduleUnprimeVars(),false);
		return returned_path;
	}
	public BDD[] EG_example(BDD s,BDD f) {
		BDD feasible=getDesign().feasible().and(f);
		BDD temp, fulfill;
		// saving to the previous restriction state
		Vector<BDD> trans_restrictions = design
				.getAllTransRestrictions();

		// Lines 1-2 are handled by the caller. ("verify")

		// Line 3
		design.restrictTrans(feasible.and(Env.prime(feasible)));

		// Line 4
		    //feasible.satOne(design.moduleUnprimeVars(), false); **************
		// BDD s = feasible.satOne();

		// Lines 5-6
		while (true) {
			temp = design.allSucc(s).and(
					design.allPred(s).not());
			if (!temp.isZero())
				s = temp.satOne(design.moduleUnprimeVars(), false);
				// s = temp.satOne();
			else
				break;
		}
		// Lines 5-6 : better version.
		// temp = tester.allSucc(s).and(tester.allPred(s).not());
		// while (!temp.isZero()){
		// s = temp.satOne(tester.moduleUnprimeVars(), false);
		// temp = tester.allSucc(s).and(tester.allPred(s).not());
		// }

		// Line 7: Compute MSCS containing s.
		BDD feas = design.allSucc(s);

		// Line 9
		// Find prefix - shortest path from initial state to subgraph feas.
		design.removeAllTransRestrictions();
		Vector<BDD> prefix = new Vector<BDD>();
		BDD[] path = design.shortestPath(design.initial(),
				feas);
		for (int i = 0; i < path.length; i++)
			prefix.add(path[i]);

		// //// Calculate "_period".

		// Line 8: This has to come after line 9, because the way TS.tlv
		// implements restriction.
		design.restrictTrans(feas.and(Env.prime(feas)));

		// Line 10
		Vector<BDD> period = new Vector<BDD>();
		period.add(prefix.lastElement());

		// Since the last item of the prefix is the first item of
		// the period we don't need to print the last item of the prefix.
		temp = prefix.remove(prefix.size() - 1);

		// Lines 11-13
		if (design instanceof ModuleWithWeakFairness) {
			ModuleWithWeakFairness weakDes = (ModuleWithWeakFairness) design;
			for (int i = 0; i < weakDes.justiceNum(); i++) {
				// Line 12, check if j[i] already satisfied
				fulfill = Env.FALSE();
				for (int j = 0; j < period.size(); j++) {
					fulfill = period.elementAt(j).and(weakDes.justiceAt(i))
							.satOne(weakDes.moduleUnprimeVars(), false);
					// fulfill =
					// period.elementAt(j).and(design.justiceAt(i)).satOne();
					if (!fulfill.isZero())
						break;
				}
				// Line 13
				if (fulfill.isZero()) {
					BDD from = period.lastElement();
					BDD to = feas.and(weakDes.justiceAt(i));
					path = weakDes.shortestPath(from, to);
					// eliminate the edge since from is already in period
					for (int j = 1; j < path.length; j++)
						period.add(path[j]);
				}
			}
		}
		// Lines 14-16
		if (design instanceof ModuleWithStrongFairness) {
			ModuleWithStrongFairness strongDes = (ModuleWithStrongFairness) design;
			for (int i = 0; i < strongDes.compassionNum(); i++) {
				if (!feas.and(strongDes.pCompassionAt(i)).isZero()) {
					// check if C requirement i is already satisfied
					fulfill = Env.FALSE();
					for (int j = 0; j < period.size(); j++) {
						fulfill = period.elementAt(j).and(
								strongDes.qCompassionAt(i)).satOne(
								strongDes.moduleUnprimeVars(), false);
						// fulfill =
						// period.elementAt(j).and(design.qCompassionAt(i)).satOne();
						if (!fulfill.isZero())
							break;
					}

					if (fulfill.isZero()) {
						BDD from = period.lastElement();
						BDD to = feas.and(strongDes.qCompassionAt(i));
						path = strongDes.shortestPath(from, to);
						// eliminate the edge since from is already in period
						for (int j = 1; j < path.length; j++)
							period.add(path[j]);
					}
				}
			}
		}

		//
		// Close cycle
		//

		// A period of length 1 may be fair, but it might be the case that
		// period[1] is not a successor of itself. The routine path
		// will add nothing. To solve this
		// case we add another state to _period, now it will be OK since
		// period[1] and period[n] will not be equal.

		// Line 17, but modified
		if (!period.firstElement().and(period.lastElement()).isZero()) {
			// The first and last states are already equal, so we do not
			// need to extend them to complete a cycle, unless period is
			// a degenerate case of length = 1, which is not a successor of
			// self.
			if (period.size() == 1) {
				// Check if _period[1] is a successor of itself.
				if (period.firstElement().and(
						design.succ(period.firstElement())).isZero()) {
					// period[1] is not a successor of itself: Add state to
					// period.
					period
							.add(design
									.succ(period.firstElement())
									.satOne(
											design
													.moduleUnprimeVars(), false));
					// period.add(design.succ(period.firstElement()).satOne());

					// Close cycle.
					BDD from = period.lastElement();
					BDD to = period.firstElement();
					path = design.shortestPath(from, to);
					// eliminate the edges since from and to are already in
					// period
					for (int i = 1; i < path.length - 1; i++)
						period.add(path[i]);
				}
			}
		} else {
			BDD from = period.lastElement();
			BDD to = period.firstElement();
			path = design.shortestPath(from, to);
			// eliminate the edges since from and to are already in period
			for (int i = 1; i < path.length - 1; i++)
				period.add(path[i]);
		}

		// Yaniv - the last one is for closing the cycle. He won't be printed.
		period.add(period.firstElement());

		// There is no need to have the last state of the period
		// in the counterexample since it already appears in _period[1]
		// if (period.size() > 1)
		// temp = period.remove(period.size() -1);

		// Copy prefix and period.
		prefix.addAll(period);
		BDD[] returned_path = new BDD[prefix.size()];
		prefix.toArray(returned_path);
		for (int i = 0; i < returned_path.length; i++) {
			returned_path[i] = returned_path[i].satOne(getDesign().moduleUnprimeVars(), false);
		}
		// returning to the previous restriction state
		design.setAllTransRestrictions(trans_restrictions);
		return returned_path;
	}
	public BDD[] EBU_example(BDD s,int from, int to, BDD f, BDD g){
		BDD[] Z = new BDD[100];
		int m=0,n=from;
		BDD oldZ=null;
		Z[to]=g.id().and(getDesign().feasible());
		for(int i=to-1;i>=from;i--)
		{
			Z[i] = Z[i+1].or(f.and(design.pred(Z[i+1])));
			if(Z[i].equals(Z[i+1])) {n=i;break;}
			n=i;
		}
		oldZ=Z[n];
		for(int i=from-1;i>=0;i--)
		{
			Z[i] = f.and(design.pred(oldZ));
			if(Z[i].equals(oldZ)) {m=i;break;}
			oldZ=Z[i];
			m=i;
		}
		//System.out.println("--n--"+n+"--m--"+m);
		BDD [] return_path=new BDD[100];
		BDD c=s,next;
		if (Z[m]==null)
		{       m=n;
				return_path[0]=c.and(Z[m]).satOne(getDesign().moduleUnprimeVars(),false);
			return return_path;
		}
		else
		{
		for(int i=0;i<=m ;i++)//补齐0 ---- m
		{
			return_path[i]=c.and(f).and(Z[m]).satOne(getDesign().moduleUnprimeVars(),false);
			next=getDesign().succ(c);
			c=next;
			//System.out.println(i+"---"+return_path[i]);
		}
		for(int i=m+1;i<=from-1;i++)//补齐m+1 ---- from-1
		{
			return_path[i]=getDesign().succ(return_path[i-1]).and(Z[i]).satOne(getDesign().moduleUnprimeVars(),false);
			//System.out.println(i+"---"+return_path[i]);
		}
/*
方法1
 */
//		int stop=0;
//		for(int i=from;i<=n  ;i++)//补齐from ---- n
//		{
//			return_path[i]=getDesign().succ(return_path[i-1]).and(Z[n]).satOne(getDesign().moduleUnprimeVars(),false);
//			//System.out.println(i+"---"+return_path[i]);
//			if (!return_path[i].and(g.id()).equals(Env.FALSE())) {stop=1;break;}//*******
//		}
//		if(stop==0)//stop=1 提前结束无需补齐
//		{
//			int i=n;
//			while(return_path[i].and(g.id()).equals(Env.FALSE())){//补齐n ---- to
//				return_path[i+1]=getDesign().succ(return_path[i]).and(Z[i+1]).satOne(getDesign().moduleUnprimeVars(),false);
//				i=i+1;
//				//System.out.println(i+"---"+return_path[i]);
//			}
//		}
//
/*
方法2
 */
		BDD nextZ,nextg;
		for(int i=from;i<=to  ;i++)//补齐from ---- n --- to
		{
			if(i<=n) nextZ=Z[n];
			else nextZ=Z[i];
			nextg=getDesign().succ(return_path[i-1]).and(nextZ).and(g.id());
			if (!nextg.equals(Env.FALSE())) {
				return_path[i]=nextg.satOne(getDesign().moduleUnprimeVars(),false);
				break;
			}
			return_path[i]=getDesign().succ(return_path[i-1]).and(nextZ);
		}
		return return_path;
		}
	}
	public BDD[] EBG_example(BDD s,int from, int to, BDD f){
		BDD[] Z = new BDD[100];
		int m=0,n=0;
		BDD oldZ=null;
		Z[to]=f.id().and(getDesign().feasible());
		for(int i=to-1;i>=from;i--)
		{
			Z[i] = Z[i+1].or(f.and(design.pred(Z[i+1])));
			if(Z[i].equals(Z[i+1])) {n=i;break;}
			n=i;
		}
		oldZ=Z[n];
		for(int i=from-1;i>=0;i--)
		{
			Z[i] = design.pred(oldZ);
			if(Z[i].equals(oldZ)) {m=i;break;}
			oldZ=Z[i];
			m=i;
		}//from 为0跳过此步

		BDD [] return_path=new BDD[100];
		BDD c=s,next;

		if(Z[m]==null)//0..n
		{
			m=n;
			for(int i=0;i<=to ;i++)
			{
				return_path[i]=c.and(Z[m]).satOne(getDesign().moduleUnprimeVars(),false);
				next=getDesign().succ(c);
				c=next;
				//System.out.println(i+"---"+return_path[i]);
			}
			return return_path;
		}
        else
		{
		if (s.and(Z[m]).equals(Env.FALSE()))return null;
		for(int i=0;i<=m ;i++)//补齐0 ---- m
		{
			return_path[i]=c.and(Z[m]).satOne(getDesign().moduleUnprimeVars(),false);
			next=getDesign().succ(c);
			c=next;
			//System.out.println(i+"---"+return_path[i]);
		}
		for(int i=m+1;i<=from-1;i++)//补齐m+1 ---- from-1
		{
			return_path[i]=getDesign().succ(return_path[i-1]).and(Z[i]).satOne(getDesign().moduleUnprimeVars(),false);
			//System.out.println(i+"---"+return_path[i]);
		}
		int stop=0;
		for(int i=from;i<=n  ;i++)//补齐from ---- n
		{
			return_path[i]=getDesign().succ(return_path[i-1]).and(Z[n]).satOne(getDesign().moduleUnprimeVars(),false);
			//System.out.println(i+"---"+return_path[i]);
		}
		for(int i=n;i<=to-1;i++)//补齐n ---- to
		{
			return_path[i+1]=getDesign().succ(return_path[i]).and(Z[i+1]).satOne(getDesign().moduleUnprimeVars(),false);
			//System.out.println(i+"---"+return_path[i]);
		}
		return return_path;
		}
	}
	/*
	end counterexample
	 */
}
