import YM.Next.RANK.Compass
import YM.Next.RANK.GlowLine
import YM.Next.RANK.LeadingLine
import YM.Next.RANK.ScaleScale

/-!
# Remainders in origin keys

Convert the linear-cell rays to tilted/clothed Key variables at Frame weights. Trim comparisons
still apply even if ℋ weights on residual terms vary. -/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Rank.Spindle
open Function Filter Set Lattice Wilson RG Labels Source Source.Drops MvPolynomial Normal LiftMark Configuration Atlas CellsInt Asymptotics MeasureTheory Rise
open scoped Classical Topology Matrix.Norms.Frobenius BigOperators

variable {G : Gauge} {A V W : Type*} {n : Side} {o : Site n} {d b R : ℕ}

lemma flash_coord (p : Snap G d) (i : KeyIn G d) (h : ℝ) : kp d (flash p h) i= (h:ℂ)^(key G d i) * kp d p i := by
  have hi:= (spanKey d i).isLt; change i.val.1<d-1 at hi
  unfold kp Labels.coord flash; simp only [expand,Source.Drops.trunk,dif_pos hi,scaleJet,map_smul,Finsupp.smul_apply,smul_eq_mul, Complex.ofReal_mul,Complex.ofReal_pow]; rfl
lemma kp_real (p : Snap G d) (i) : (((kp d p i).re:ℝ):ℂ)=kp d p i := rfl
lemma kp_contains (u : KeyIn G d → ℝ) : ∃ A : Snap G d, kp d A = fun i => (u i:ℂ) := by
  let q (i : Key G) := if h : Labels.generation i≤d then u ⟨i,h⟩ else 0
  let A j:= (Labels.axes G j).equivFun.symm fun k => q ⟨j,k⟩
  refine ⟨Drops.trunk d A, funext fun i=>?_⟩
  let p:= i.val
  unfold kp Labels.coord
  rw [expand, dif_pos (show p.1<d-1 from (spanKey d i).isLt)]
  change (((Labels.axes G _).equivFun (A p.1) p.2:ℝ):ℂ)=(u i:ℂ)
  unfold A; rw [LinearEquiv.apply_symm_apply]
  change (q p:ℂ)=_; unfold q; rw [dif_pos i.property]

lemma circle (g : Label G d) : trim (thawKey g) (key G d) d=thawKey g := by
  apply rename_injective (R:=ℂ) (f:=(Subtype.val : KeyIn G d → Key G)) (by exact Subtype.val_injective)
  rw [← show _=rename (Subtype.val : KeyIn G d→ Key G) (trim (thawKey g) (key G d) d) from trim_rename _ generation (thawKey g) d, returns]
  ext i; rw [Rise.trim_coeff]; split
  · rfl
  symm; apply MvPolynomial.notMem_support_iff.mp
  intro hi; have he : Finsupp.weight Labels.generation i ≤ d := (show g.val∈limited G d from g.property.1) (by exact hi)
  contradiction
lemma spots_output (g : poly (KeyIn G d)) : ∀ i ∈ (trim g (key G d) d).support,Finsupp.weight (key G d) i ≤ d := by
  intro i hi; have he:= MvPolynomial.mem_support_iff.mp hi; rw [Rise.trim_coeff] at he
  split at he; assumption; contradiction
lemma rewrites (P : Label G d) (A : Jet G) :
    Labels.read A P.val=aeval (kp d (Drops.trunk d A)) (thawKey P) := by
  rw [← Source.Drops.racts, ← returns P]
  apply DFunLike.congr_fun (f:=(Labels.read (expand d (Drops.trunk d A))).comp (rename Subtype.val))
  ext i; rw [AlgHom.comp_apply,rename_X,Labels.read]; simp only [aeval_X]; rfl

-- pay Gibbs h ray, trim high for ANY key polynomial
lemma settled_ray (z : Snap G d) (i : KeyIn G d) : ContDiff ℝ d (fun t => kp d (flash z t) i) := by simp_rw [flash_coord]; exact (Complex.ofRealCLM.contDiff.pow _).mul contDiff_const
lemma okAt (A : Snap G d) (P : poly (KeyIn G d)) : ContDiffAt ℝ d (fun t => aeval (kp d (flash A t)) P) 0 := walks (fun i t=> kp d (flash A t) i) _ (fun i => (settled_ray A i).contDiffAt) P
lemma verses (y : poly (KeyIn G d)) (A : Snap G d) :
    let t := trim y (key G d) d
    asym d ((fun r : ℝ => aeval (kp d (flash A r)) y) -(fun r : ℝ => aeval (kp d (flash A r)) t)) ∧ ∃ f,
      (fun r : ℝ => aeval (kp d (flash A r)) t)=Dims d f := by
  let F (p : poly (KeyIn G d)) (r : ℝ) := aeval (kp d (flash A r)) p
  let X:= key G d
  have hp x c h : F (monomial x c) h= h^(Finsupp.weight X x) • F (monomial x c) 1 := by
    simp_rw [F, show kp d (flash A 1)=kp d A from funext fun i => by rw [flash_coord, Complex.ofReal_one,one_pow,one_mul]]
    rw [show kp d (flash A h) = rays X _ h from funext (fun i => flash_coord A i h)]; exact told ..
  intro t; refine ⟨?_,?_⟩
  · let s := y.support.filter (fun i => ¬Finsupp.weight X i ≤ d)
    have ht : F y-F t= ∑ i∈ s, F (monomial i (coeff i y)) := by
      funext i; rw [Pi.sub_apply]; unfold F; rw [← map_sub,Rise.above,map_sum,Finset.sum_apply]
    change asym d (F y-F t); rw [ht]
    rw [show (∑ i∈s, F (monomial i (coeff i y)))=fun p=> ∑ i∈s,F (monomial i (coeff i y)) p from _root_.funext (fun x=> Finset.sum_apply _ _ _)]
    apply Asymptotics.IsLittleO.sum; intro i hi
    have hi := Finset.mem_filter.mp hi
    let v:=Finsupp.weight X i; let P:=monomial i (coeff i y)
    change asym d (F P); rw [show F P=fun h:ℝ => h^v • F P 1 from _root_.funext (hp i (coeff i y))];
    refine (show (fun h : ℝ => h^v • F P 1)=O[𝓝 0] (fun h:ℝ => h^v) from isBigO_iff.mpr ?_).trans_isLittleO (isLittleO_pow_pow (show d<v from Nat.lt_of_not_ge hi.2))
    exact ⟨‖F P 1‖,Eventually.of_forall fun x=>by rw [norm_smul,mul_comm]⟩
  refine ⟨sound X t (kp d A),?_⟩
  simp_rw [show ∀ r,kp d (flash A r)= rays X (kp d A) r from fun r => funext (fun i=> flash_coord A i r)]
  exact toller X t _ _ (spots_output y)
lemma ray_stamp (z : Snap G d) (p : poly (KeyIn G d)) : evaluate_ray (fun t => aeval (kp d (flash z t)) p) d=
    aeval (kp d z) (trim p (key G d) d) := by
  let v:= trim p (key G d) d; obtain ⟨hX,hP⟩ := verses p z
  let F (p : poly (KeyIn G d)) (r:ℝ) := aeval (kp d (flash z r)) p
  change evaluate_ray (F p) d= _
  calc
    _ = evaluate_ray (F v) d := trill d (okAt z p) (okAt z v) hX
    _ = F v 1 := total_set d (okAt z v) hP
    _ = _ := by unfold F; rw [show kp d (flash z 1)=kp d z from funext fun i => by rw [flash_coord,Complex.ofReal_one,one_pow,one_mul]]

-- formal input L inside Frame. Positions all in one $trimV$ when legal.
abbrev slotC (G : Gauge) (b : ℕ) := Turn b × G.ColorIndex

def calls (h : 4*b≤R) (i : slotC G b) : trimV R G := by
  refine ⟨(i.1.val.1,i.1.val.2,i.2),(tracing ..).2 ((bounded (faceOrigin i.1)).trans h)⟩

-- first projection to Word sum in Spindle.Patch coordinates. X(k) probe realization.
def sum_line (l : Word b) (i : G.ColorIndex) : slotC G b →₀ ℂ := List.sum (l.map fun p => Finsupp.single (p.1,i) (if p.2 then -1 else 1))

def visit (h : 2*(b+1)<n.val) (i : links G o b) := sum_line (word G h i.1) i.2
def dustAt {o : Site n} (h : 2*(b+1)<n.val) (B : poly (links G o b)) := exchange (visit h) B

lemma cooked (p : Word b) (U : Turn b→ G.Color) (i : G.ColorIndex) : aeval (fun x : slotC G b => (U x.1 x.2:ℂ)) (glyph (sum_line p i))=
    (stage p U i:ℂ) := by
  induction p with
  | nil => simp only [sum_line,List.map_nil,List.sum_nil,glyph,map_zero,stage];rfl
  | cons a p H =>
    let P := glyph (sum_line p i); let Y (x : slotC G b) := (↑(U x.1 x.2):ℂ)
    change aeval Y (_ : poly (slotC G b))=_
    rw [show sum_line (a::p) i= Finsupp.single (a.1,i) (if a.2 then -1 else 1) + sum_line p i from rfl]; unfold glyph;rw [map_add,map_add,Finsupp.linearCombination_single, map_smul,aeval_X, show aeval Y (Finsupp.linearCombination ℂ _ _) = _ from H]
    cases hn : a.2
    · change (if false=true then _ else 1) • (↑(U a.1 i):ℂ) + ↑(stage p U i)=_
      unfold stage; simp only [hn,Bool.false_eq_true,↓reduceIte,List.map_cons,List.sum_cons,one_smul]; rw [← Complex.ofReal_add];rfl
    unfold stage; simp only [hn,↓reduceIte,List.map_cons,List.sum_cons,neg_smul,one_smul]
    unfold Y; rw [← Complex.ofReal_neg,← Complex.ofReal_add]; rfl
lemma full_dust (h : 2*(b+1)<n.val) (U : Turn b→ G.Color) (B : poly (links G o b)) :
    text (fun i : slotC G b => U i.1 i.2) (dustAt h B) = text (scan (rows (o:=o) 1 h U)) B := by
  apply DFunLike.congr_fun (f:= (aeval (R:=ℂ) (fun x : slotC G b => (↑(U x.1 x.2):ℂ))).comp (exchange (visit (o:=o) h)))
  ext1 i; rw [AlgHom.comp_apply, exchange_x,visit,cooked, aeval_X]; unfold scan rows; simp

def unwind {o : Site n} (h : 2*(b+1)<n.val) (r : 4*b≤R) (d : ℕ) :=
    ((exchange (ink d (Subtype.val : trimV R G→Beamer.Address G))).comp (rename (calls r))).comp (exchange (visit (G:=G) (o:=o) h))
lemma veneer {o : Site n} (H : Hol G) (h : 2*(b+1)<n.val) (r : 4*b ≤ R) (A : Snap G d) (B : poly (links G o b)) :
    walked (tacks H h A) B=fun p:ℝ => aeval (kp d (flash A p)) (unwind h r d B) := by
  funext u; let F:= flash A u
  have he (i : slotC G b) : aeval (kp d F) (Normal.glyph (ink d Subtype.val (calls r i)))=(lamp d F i.1 i.2:ℂ) := by
    let q:= i.1.val
    simp only [ink,glyph, map_sum, Finsupp.linearCombination_single,map_smul,aeval_X]
    change _ = (↑(oneGlow d F q i.2):ℂ); rw [traffic, Complex.ofReal_sum]; apply Finset.sum_congr rfl; intro j _; rw [Complex.ofReal_mul, kp_real]; change (↑(_ : ℝ):ℂ) * kp d F _=kp d F _* _; exact mul_comm ..
  apply DFunLike.congr_fun (g:=(aeval (R:=ℂ) (kp d F)).comp (unwind (o:=o) h r d))
  ext1 i; simp only [unwind,AlgHom.comp_apply,exchange_x,visit]
  have hE : ((aeval (R:=ℂ) (kp d F)).comp (exchange (ink d (Subtype.val : trimV R G→Beamer.Address G)))).comp (rename (calls r))=aeval (fun i : slotC G b => (lamp d F i.1 i.2:ℂ)) := by
    ext1 j; simp only [AlgHom.comp_apply,rename_X,exchange_x,aeval_X]; exact he j
  apply Eq.trans _ (DFunLike.congr_fun hE (glyph (sum_line (word G h i.1) i.2))).symm
  rw [aeval_X]; change tacks H h A i u=aeval _ (glyph (sum_line _ _)); rw [cooked (U:=lamp d F)]
  exact congr_arg (fun c : G.Color=>((c i.2):ℂ)) (lumen H d _ h i.1 F)

lemma prices (l : Word b) (i : G.ColorIndex) : coin (glyph (sum_line l i))≤ l.length := by
  induction l with
  | nil => simp [coin,glyph,sum_line,Rise.pay_nothing]
  | cons a p H =>
    rw [show sum_line (a::p) i= Finsupp.single (a.1,i) (if a.2 then -1 else 1) + sum_line p i from rfl,List.length_cons]
    push_cast
    unfold glyph; rw [map_add]; apply (Rise.taller _ zero_le_one ..).trans
    rw [Finsupp.linearCombination_single]
    split
    all_goals refine (add_le_add (le_trans (retiring _ _) ?_) H).trans_eq (add_comm 1 _)
    all_goals simp [coin]
end YM.Next.Rank.Spindle
