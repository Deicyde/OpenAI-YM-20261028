import YM.RG08.Room.Alight

/-!
# Intertwine shifted evaluation with the same finite prescription used for cover kernels.
Supply raw heat on a (possibly larger) alphabet I, and centered heat kernel `S` on test J
(only a subset foam_J actually integrated, including singular symbols at others). Check
conjugation of prices incl colors literally, and derivative of ring pullback from I to J;
do NOT require rank of either if passing evaluated means this way.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG08.Room
open Forms Glyph Cloud Finset Function MvPolynomial
open scoped PowerSeries BigOperators Topology Classical
variable {I J:Type}[Fintype I][Fintype J]
 set_option linter.unusedSectionVars false
namespace Haze
variable {S:Haze J}{A:Line I}{L:I→J→ℝ}

def Relation (S:Haze J)(A:Line I)(L:I→J→ℝ):Prop:=∀ i k,∑ a∈S.foam,∑ b∈S.foam,S.price a b*L i a*L k b=A i k

set_option linter.unusedSimpArgs false in
lemma meditation (L:I→J→ℝ)(k:J)(p:Inn I): pderiv k (twistMean L p)=∑ i,L i k • twistMean L (pderiv i p):=by
 have he(i:I):pderiv k (twistMean L (X i))=C (L i k):=by
    rw [twistMean,aeval_X,median,map_sum]
    simp only [Derivation.map_smul,pderiv_X,Pi.single_apply,smul_ite,smul_zero,sum_ite_eq',if_pos (mem_univ _)] -- orientation?
    rw [Algebra.smul_def,mul_one];rfl
 induction p using MvPolynomial.induction_on with
 | C=>simp [twistMean]
 | add _ _ ha hb=>simp only [map_add,ha,hb,Finset.sum_add_distrib,smul_add]
 | mul_X p i h=>
   rw [_root_.map_mul,pderiv_mul,h,he];simp only [pderiv_mul,map_add,map_mul,smul_add,Finset.sum_add_distrib,Finset.sum_mul,smul_mul_assoc];simp only [pderiv_X,Pi.single_apply,apply_ite,map_one,map_zero,mul_one,mul_zero,smul_zero,Finset.sum_ite_eq]; rw [if_pos (mem_univ _),Algebra.smul_def,mul_comm _ (C _)];rfl

lemma mirror (h:Relation S A L)(p:Inn I):radiator S.price (twistMean L p)=twistMean L (radiator A p):=by
 simp_rw [radiator,slab_do,axes,meditation,map_sum,Derivation.map_smul, meditation,_root_.map_smul]
 -- limit a,b to foam
 let U j k: Inn J:=twistMean L (pderiv k (pderiv j p))
 let W(a b:J):Inn J:=half S.price a b • ∑ i,L i b • ∑ k,L k a • U i k
 change ∑ a,∑ b,W a b=_
 have he : (∑ a∈S.foam,∑ b∈S.foam,W a b)=∑ a,∑ b,W a b:=by
   calc
   _=∑ a∈S.foam,∑ b,W a b:=Finset.sum_congr rfl fun a _=>Finset.sum_subset (subset_univ _) (fun b _ hb=>by simp [W,half,S.dryR _ _ hb])
   _= _:=Finset.sum_subset (subset_univ _) (fun a _ ha=>Finset.sum_eq_zero fun b _=>by simp [W,half,S.dryL _ _ ha])
 rw [←he]; unfold W; simp_rw [Finset.smul_sum,smul_smul];rw [Glyph.square S.foam S.foam,Finset.sum_comm (s:=univ (α:=I)) (t:=univ (α:=I))];apply Finset.sum_congr rfl;intro i _;apply Finset.sum_congr rfl;intro k _;simp_rw [←Finset.sum_smul]
 change _ • U k i= half _ _ _ • U k i
 congr 1;simp only [half,←h i k,Finset.sum_div];apply Finset.sum_congr rfl;intro a _;apply Finset.sum_congr rfl;intro b _;ring

def mView (S:Haze J)(L:I→J→ℝ)(i:I)(j:J):ℝ:=if j∈S.foam then 0 else L i j
set_option linter.unusedSimpArgs false in
private lemma stillpoint (p:Inn I):aeval S.stop (twistMean L p)=twistMean (mView S L) p:=by
 induction p using MvPolynomial.induction_on with
 | C a=>unfold twistMean;simp
 | add _ _ ha hb=>simp only [map_add,ha,hb]
 | mul_X p i h=>
   rw [_root_.map_mul,_root_.map_mul,_root_.map_mul,h];congr 1
   simp_rw [twistMean,aeval_X,median,map_sum] -- no aeval_X until sum
   simp only [_root_.map_smul,MvPolynomial.aeval_X,stop,mView]
   apply sum_congr rfl;intro j _;split <;> simp_all

lemma locked (h:Relation S A L)(hΓ:∀ i k,A i k=A k i)(p:Inn I): S.stove (twistMean L p)=twistMean (mView S L) (wick A p):=by
 have he(i:ℕ)(p:Inn I):(radiator S.price)^[i] (twistMean L p)=twistMean L ((radiator A)^[i] p):=by
    induction i with
    | zero=>rfl
    | succ i hh=> rw [iterate_succ_apply',hh,mirror h,iterate_succ_apply']
 obtain ⟨n,hn⟩:=halts A hΓ p
 have ht(i):gust S.price i (twistMean L p)=twistMean L (gust A i p):=by unfold gust;rw [he,_root_.map_smul]
 have hp:Halt S.price (twistMean L p) n:=fun i hi=>by rw [ht,hn _ hi,map_zero]
 change aeval _ (wick _ _)=_
 rw [wick_budget hn,wick_budget hp,map_sum,map_sum];apply Finset.sum_congr rfl;intro i _;rw [ht,stillpoint]

private def phase (L:I→J→ℝ)(i:I):Port J:=liftInn (median L i)
private lemma shoot (f:Inn I):belt (phase L) (liftInn f)=liftInn (twistMean L f):=by
 rw [belt_c];induction f using MvPolynomial.induction_on with
 | C a=>unfold lug twistMean;rw [aeval_C,aeval_C,PowerSeries.algebraMap_apply]
 | add a b hi hj=>rw [_root_.map_add,_root_.map_add,_root_.map_add,hi,hj]
 | mul_X a i ha=>rw [_root_.map_mul,_root_.map_mul,_root_.map_mul,ha]; unfold lug twistMean;rw [aeval_X,aeval_X];rfl

lemma reflected (f:Port I)(e:ℕ):tap e (belt (fun i=>liftInn (median L i)) f)=twistMean L (tap e f):=by
 let b:=tube (PowerSeries.C:Inn I→Cab (Inn I)) f e
 have he(i)(hi:i≤e):tap i f=tap i b:=by unfold b;rw [←tubes _ _ _ _ hi,direct]
 change tap e (belt (phase L) f)=_
 rw [steady_belt (phase L) e f b he];unfold b tube; rw [map_sum]
 unfold tap;rw [map_sum,sum_eq_single e (by
   intro i _ hi
   change PowerSeries.coeff e (belt (phase L) (liftInn _*PowerSeries.X^i))=_
   rw [_root_.map_mul,_root_.map_pow,belt_g,shoot,PowerSeries.coeff_C_mul_X_pow,if_neg (Ne.symm hi)]) (by simp)]
 change PowerSeries.coeff e (belt (phase L) (liftInn _*PowerSeries.X^e))=_
 rw [_root_.map_mul,_root_.map_pow,belt_g,shoot,PowerSeries.coeff_C_mul_X_pow,if_pos rfl]

/-- Conditioning in centered gauss is exactly the requested Glyph.house incl substitutions on
survivors. raw padded prices, no scalar volume limits. Ensure L outside H'.foam is exactly given
mean on those coordinates (and no Glyph output on integrated coords with this version).
-/
theorem stood (h:Relation S A L)(hh:∀ i k,A i k=A k i)(f:Port I): S.brew (belt (fun i=>liftInn (median L i)) f)=house A (mView S L) f:=by
 ext e :1
 change tap _ _=_;rw [brew_view,reflected,locked h hh,house,PowerSeries.coeff_map,sky,PowerSeries.coeff_mk];rfl
end Haze
end YM.RG08.Room
