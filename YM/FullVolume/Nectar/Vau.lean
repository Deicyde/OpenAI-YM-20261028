import YM.FullVolume.Nectar.Award
set_option autoImplicit false
noncomputable section
namespace YM.FullVolume.Nectar
open RG Set Finset Filter Ray Function PhysicalNext.Repeat PhysicalNext.Repeat.Luna.Aank Paint Tower Amp Beam
open scoped Topology BigOperators Classical ENNReal
open MergeProof MergeProof.Accent Marker Push Push.AbsoluteSums Lattice Wilson Tint GridApprox.Nil
variable {X I J:Type}{v a b t u d p c:ℝ}
variable {V : Type}[DecidableEq V][Fintype V] {B:Census V}
variable {G:Gauge}{n:Side}
variable {w:V→ℝ} {F:sun→X→Poly B}(hw:∀ i,0<w i)
namespace LeafPaid
lemma cutoff (S:Set X)(h:LeafPaid w F a): LeafPaid w (fun t=> S.indicator (F t)) a:=by
  obtain ⟨v,hv,ha,h⟩:=h; refine ⟨v,hv,ha,fun i=> Eq.mp ?_ ((h i).cropped S)⟩;congr! with x y; by_cases h:y∈S <;> simp [h]
lemma daisy (F: I→sun→X→Poly B)(s: Finset I) (p:I→ℝ)(hp: ∀ i∈s,LeafPaid w (F i) (p i)): LeafPaid w (fun t y=>∑ i∈ s,F i t y) (∑ i∈s,p i):=by
   have ha i: ∃ v:Sheet B, 0≤v∧ (i∈s→ wordsPrice w v ≤ p i ∧ ∀ j,Feel (fun t u=>(F i t u).part j) (v j)):= by
     by_cases h:i∈s;obtain ⟨v,hv,hx,hQ⟩:=hp i h; exact ⟨_,hv,fun _=> ⟨hx,hQ⟩⟩; exact ⟨0,le_rfl, fun z=>(h z).elim⟩
   choose v hv h using ha
   refine ⟨fun j=>∑ i∈s,v i j,fun j=>sum_nonneg (fun i _=>hv i j),?_,fun i=>?_⟩
   · unfold wordsPrice; simp_rw [mul_sum]; rw [sum_comm];exact Finset.sum_le_sum fun i hi=> (h i hi).1
   simp_rw [Poly.part_sum]; exact Feel.stacks s _ _ (fun j hj=> (h j hj).2 i)
include hw in
lemma pricesN (h:LeafPaid w F a): 0≤ a:= by obtain ⟨b,hb,H,hx⟩:=h; exact (sum_nonneg fun x _=> mul_nonneg (Poly.worth hw _).le (hb x)).trans H
end LeafPaid
def Polaris (w:V→ℝ)(q:I→ Support n)(F:sun→I→X→Poly B)(b:ℕ)(d c:ℝ):Prop:= ∃ a,Summable a∧ Ac.Hit q b a d c ∧ ∀ i, LeafPaid w (fun t=>F t i) (a i)
namespace Polaris
variable [Fintype I] {b':ℕ}
variable {F:sun→I→ X→Poly B}
include hw
lemma together [Fintype J] (k:I→J) (r:J→Support n) (h:Polaris w (r∘k) F b' d c): Polaris w r (fun t=> Accent.tally k (F t)) b' d c :=by
    obtain ⟨a,ha,hb,hX⟩:=h; let f(j:J):=∑ i:{i// k i=j}, a i.val; refine ⟨f,Summable.of_finite,fun x=> ?_,fun p=>?_⟩
    · let P i:= if x∈ (r ∘ k) i then a i*Real.exp (d* ↑(coverNumber b' ((r ∘ k) i))) else 0
      have ht: SumBudget P c:=hb x; have hx:=heavy k ht.2.1
      convert (show SumBudget (cram k P) c from ⟨fun _=> tsum_nonneg (fun i=> ht.1 i.val), hx.summable,hx.tsum_eq.trans_le ht.2.2⟩) using 1; ext j; unfold cram; rw [tsum_fintype]; unfold P; dsimp only [Function.comp_apply]; simp_rw [fun x:{i//k i=j}=> x.property];split_ifs
      · unfold f;exact Finset.sum_mul ..
      simp
    unfold Accent.tally; simp_rw [tsum_fintype]; exact LeafPaid.daisy (w:=w) (fun (i:{i// k i=p}) t=> F t i.val) Finset.univ _ fun i _=>hX _
-- exclude projection. choose fee exponent exactly fixed.Z
lemma glimmers (K:sun→MergeProof.Box n→ Config G n→Poly B)(U: sun →I→ Config G n→Poly B) (X:I→Support n) (e:ℝ)
    (hp:Polaris w Prod.fst K b' (d+a) p)(hv:Polaris w X U b' (d+a) v)(ha:0≤d)(ht:((b'+b'+1:ℕ):ℝ)^4*(p+v)≤a): Polaris w Prod.fst (fun t=> Accent.closure (K t) (U t) X e) b' d (Real.exp (p+v)-1):=by
   apply together (X:=Config G n) hw (forst X) Prod.fst (F:= fun t=> crow (K t) (U t) X e); let s:= bloom X
   obtain ⟨u,hu,hA,h⟩:=hp; obtain ⟨f,hf,hB,hp⟩:=hv
   let g(i : FlowKind I n):= i.elim u f; have hv i : LeafPaid w (fun t=> pork (K t) (U t) i) (g i):= by cases i; exact h _; exact hp _
   have hG i : 0 ≤ g i:= LeafPaid.pricesN hw (hv i)
   let e'(i:Period X):= ∏ j∈i.val,g j
   have ht' : Ac.Hit s b' g (d+a) (p+v) := by
     intro i
     refine Extra.Multi.Budget.certify (fun j=> by split; exact mul_nonneg (hG _) (Real.exp_pos _).le;exact le_rfl) fun l=>?_
     rw [sum_sum_eq_sum_toLeft_add_sum_toRight]; exact add_le_add (Extra.Multi.Budget.cap (hA i) _) (Extra.Multi.Budget.cap (hB i) _)
   have ht(z):=Ac.forest_price (f:=g) s b' ha hG ht' ht ((tsum_nonneg (ht' 0).1|>.trans (ht' 0).2.2)) z
   refine ⟨e',Summable.of_finite,fun i=> ?_, fun i=> ?_⟩
   · refine Extra.Multi.Budget.pull_le (q:=Subtype.val) (p:=fun _=>True) (ht i) (fun i=> by split; exact mul_nonneg (prod_nonneg (fun j _=> hG j)) (Real.exp_pos _).le;exact le_rfl) (fun _ _=> trivial) Subtype.val_injective.injOn (fun j _=> ?_)
     unfold Ac.roots; by_cases h:i∈ (forst X j).1
     · rw [if_pos (show i∈(Prod.fst ∘ forst X) j from h),if_pos ⟨j.property.spark,h⟩]; exact le_of_eq (mul_comm ..)
     rw [if_neg (show i∉(Prod.fst ∘ forst X) j from h),if_neg (fun hh=> h hh.2)]
   let M(t:sun)(z:I):=U t z; let A:=forst X i; let C: Set (Config G n):= {y|A.1 ∩ flags e y=A.2}; let Vt(t:sun) (x):= ∏j∈i.val, pork (K t) (U t) j x;
   change LeafPaid w (fun t=> crow (K t) (U t) X e i) (e' i); rw [show (fun t:sun=> crow (K t) (U t) X e i)=fun t:sun=> C.indicator (Vt t) from funext fun t=>funext fun q=>by
      unfold crow; dsimp only; split
      next h=> exact (indicator_of_mem (show q∈ C from h) (Vt t)).symm
      next h=> exact (indicator_of_notMem (show q∉ C from h) (Vt t)).symm]; exact LeafPaid.cutoff C (LeafPaid.bags hw i.val (fun j t=> pork (K t) (U t) j) g (fun j _=> hv j))
end Polaris
end YM.FullVolume.Nectar
