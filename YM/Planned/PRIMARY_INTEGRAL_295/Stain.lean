import YM.Planned.PRIMARY_INTEGRAL_295.Pearl
import YM.Planned.PRIMARY_INTEGRAL_295.RollFilm

/-!
# Computing the associated graded of the flat readout

The log Hessian substitution, not assuming a covariance pricing matrix.
Each direction still uses genuine holonomy/toroidal cover conventions from
`ZeroPath` first-axis log. Account exactly for weights. This is NOT yet
including the measured response error; T is always the *one* SectionData
used from the start.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Planned.PrimaryIntegral295.Film
open Filter Function Set Lattice Labels RG Wilson Source Source.Drops Precision Bloch Next.Free Place Carrier Next.Foundations
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius
variable {G : Gauge} {j m n d t : ℕ} {F : Labels.Frame G d} {M : Side}
variable (T : SectionData F) {A : Hol G} (h : T.Sound A)
variable (P : Flight j t) (k : ℝ) (hk : 0 < k) (ht : 4 ≤ t)

include h in
/-- Perturbations lowering *any one* engineering-weight input
annihilate the whole fdb outer coefficient. -/
private lemma lighter (i : F.Index) (u v : Fin n→Potential G) (w : Fin n → ℕ) (hp : ∀ j, 0<w j)
    (he : ∑ j, w j ≤ (F.grades i).1) (hx : ∀ j, u j∈rangeLt (Axis → G.Color) (w j))
    (hy : ∀ j,v j∈rangeLt (Axis → G.Color) (w j-1)) :
    iteratedFDeriv ℝ n (column T i) 0 (fun j => ping T.stencil (u j+v j))=
      iteratedFDeriv ℝ n (column T i) 0 (fun j=> ping T.stencil (u j)) := by
  classical
  let H := iteratedFDeriv ℝ n (column T i) 0
  let a (j : Fin n) (b : Bool) := if b then v j else u j
  have he' (j : Fin n) : ping T.stencil (u j+v j)=∑ b:Bool,ping T.stencil (a j b) := by simp only [a,Fintype.sum_bool,map_add]; rw [add_comm]; simp
  simp_rw [he']; change (H (fun j=>∑ b:Bool,ping T.stencil (a j b)))=_
  rw [H.map_sum (fun j b=>ping T.stencil (a j b)),Finset.sum_eq_single (fun _=>false)]; swap
  · intro b _ hb
    let g j := if b j then w j-1 else w j
    have hv (j : Fin n) : a j (b j) ∈ rangeLt (Axis→G.Color) (g j) := by cases h:b j<;> simp [h,g,hx,hy,a]
    have hh : ∑ i,g i < ∑ i,w i := by
      obtain ⟨l,hl⟩:=Function.ne_iff.mp hb
      have hF : b l=true := Bool.eq_true_of_not_eq_false hl
      refine Finset.sum_lt_sum (fun i _=>?_ ) ⟨l,Finset.mem_univ _,?_⟩
      · unfold g; split <;> omega
      unfold g; rw [if_pos hF]; have hh:=hp l; omega
    exact lower A T h i g (hh.trans_le he) _ hv
  swap; · simp
  rfl

-- A single Faa direction vector from propagating and the *same*
-- vector if not propagating. The perturbation at weight a lowers correctly.
include ht hk in
lemma coherent (hd : d≤j) (a : Fin n→ℕ) (v : Fin n→Snap G d) (hp : ∀ i, 0<a i) (hv : ∀ i, throughSlot (v i) (a i))
    (he : ∑ i,a i ≤ d) :
    let m := ∑ i,a i
    ∃ b c : Potential G, b ∈ rangeLt (Axis→G.Color) m ∧ c ∈ rangeLt (Axis→G.Color) (m-1) ∧
      iteratedFDeriv ℝ n (localLane (G:=G) (d:=d) (S:=T.stencil)) 0 v=ping T.stencil b ∧
        iteratedFDeriv ℝ n (trace T.stencil (linesOf P k) (G:=G) (d:=d)) 0 v=ping T.stencil (unitStep P.L^m • b+c) := by
  intro m
  let b : Potential G := fun x i=> iteratedFDeriv ℝ n (lane (G:=G) (d:=d) x i) 0 v
  have hf : b∈rangeLt (Axis→G.Color) m := lane_polynomial a v hv hp
  obtain ⟨f,h1,hc,h3⟩ := accepts_V k hk P ht (he.trans hd) b hf
  refine ⟨b,f-_,hf,hc,funext (launch_testable v),?_⟩
  have hn := (Cases.arity hp).trans he
  rw [show unitStep P.L ^ m • b + (f - unitStep P.L ^ m • b) = f by abel]
  ext1 v
  rw [trace_mail (stored P k hk ht) hn ..]; exact congr_fun (congr_fun h3 _) _

include h hk ht
set_option maxHeartbeats 800000 in
/-- Through the leading weight compute all mixed-slot tests, even order
zero. -/
theorem waffle (hd : d≤j) (i : F.Index) (z : Fin n → WardBin.Board G d)
    (hZ : WardBin.depth z ≤ (F.grades i).1) :
    let C := copy F i
    iteratedFDeriv ℝ n (seen T C (linesOf P k)) 0 (WardBin.chip ∘ z) =
      unitStep P.L ^ (WardBin.depth z) • iteratedFDeriv ℝ n (slant T C ∘ localLane (d:=d)) 0 (WardBin.chip ∘ z) := by
  classical
  intro C
  let f := column T i
  let v : Fin n → Snap G d := WardBin.chip ∘ z
  let A':=trace T.stencil (linesOf P k) (G:=G) (d:=d)
  let Q:=localLane (G:=G) (d:=d) (S:=T.stencil)
  have hA:=trace_smooth (G:=G) (stored P k hk ht) T.stencil d
  have hQ:=local_smooth T.stencil (G:=G) (d:=d)
  let w j := Labels.generation (WardBin.key (z j))
  change iteratedFDeriv ℝ n (f ∘ A') 0 v=unitStep P.L^(∑ j,w j) • iteratedFDeriv ℝ n (f ∘ Q) 0 v
  have hh : ContDiff ℝ ω f := column_smooth _ _
  have hw (i : Fin n) : 0 < w i := Nat.zero_lt_of_lt (show 0<w i by unfold w generation; omega)
  have hv i : throughSlot (v i) (w i) := by
    intro k hk
    have he : k≠(z i).1 := fun he=>by subst he; exact (Nat.lt_irrefl _) hk
    exact Pi.single_eq_of_ne he _
  rw [Cases.compReads hh.contDiffAt (show ContDiffAt ℝ ω A' 0 from hA.contDiffAt) le_top,
    Cases.compReads hh.contDiffAt hQ le_top, Finset.smul_sum]
  apply Finset.sum_congr rfl; intro c _
  let V i := Cases.costs c w i
  have hc : ∑ i,V i=∑ j,w j:= Cases.all c w
  have ht' : ∑ i,V i≤(F.grades i).1:=hc.trans_le hZ
  have hb (i' : Fin c.length) : V i' ≤ d := ((Finset.single_le_sum (f:=V) (fun j _=>Nat.zero_le _) (Finset.mem_univ i')).trans ht').trans (F.bound i)
  choose b g hB hg h1 h2 using fun i : Fin c.length=> coherent T P k hk ht hd (w ∘ c.emb i) (v ∘ c.emb i)
       (fun j=> hw _) (fun j=> hv _) (hb i)
  let u i := unitStep P.L^(V i)
  have hy : (fun i=> iteratedFDeriv ℝ (c.partSize i) A' 0 (v ∘ c.emb i))= fun i=>ping T.stencil (u i • b i + g i) :=funext h2
  unfold Cases.caseRead
  have h0 : Q 0=0:=local_zero _; have hx : A' 0=0:=trace_root _
  rw [hy,hx,local_zero T.stencil,show (fun i=> iteratedFDeriv ℝ (c.partSize i) (localLane (S:=T.stencil) (G:=G) (d:=d)) 0 (v ∘ c.emb i))= fun i=>ping T.stencil (b i) from funext h1]
  change iteratedFDeriv ℝ c.length (column T i) _ _ = _
  rw [lighter T h _ _ _ V (Cases.live c hw) ht' (fun i=> Submodule.smul_mem _ _ (hB i)) hg]
  simp_rw [map_smul,ContinuousMultilinearMap.map_smul_univ,u,Finset.prod_pow_eq_pow_sum, hc]
  try rfl

set_option maxHeartbeats 800000 in
/-- Up to the column's engineering weight the full archived polynomials
are this comparison, not just their detector responses. -/
lemma stamps (hd : d≤j) (i : F.Index) (hm : m ≤ (F.grades i).1) (hn : n ≤ d) :
    gradePart (m,n) (rawBook T h (stored P k hk ht) (copy F i)) =
      (((unitStep P.L^m:ℝ):ℂ)) • gradePart (m,n) (F.basis i) := by
  classical
  let a := unitStep P.L^m
  let S : Snap G d→ℂ := seen T (copy F i) (linesOf P k)
  let R : Snap G d→ℂ := slant T (copy F i) ∘ localLane
  have h1 : Parts.Safe S := seen_safe T h (stored P k hk ht) _
  have h2 : Parts.Safe R := still T h (copy F i)
  have h3 : F.basis i=Parts.archive h2 := by
    apply Eq.trans (_ : F.basis i=F.coords.symm (copy F i)) (corner T h (copy F i)).symm
    apply F.coords.injective; simp [copy]
  apply Subtype.ext
  change (gradePart (m,n) (Parts.archive h1)).val = (↑a:ℂ) • (gradePart (m,n) (F.basis i)).val
  have hh := hm.trans (F.bound i)
  rw [h3, Parts.capture h1 hh hn, Parts.capture h2 hh hn]
  unfold WardBin.tile; rw [Finset.smul_sum]; apply Finset.sum_congr rfl; intro b hb
  have hu := (Finset.mem_filter.mp hb).2
  have hev := waffle T h P k hk ht hd i b (hu.trans_le hm)
  have H : (Tensor.coeff S n 0) (WardBin.chip ∘ b) = (↑a:ℂ)* (Tensor.coeff R n 0) (WardBin.chip ∘ b) := by
    rw [← Complex.real_smul]
    change (n.factorial:ℝ)⁻¹ • iteratedFDeriv ℝ n S 0 _ = _
    change (iteratedFDeriv ℝ n S 0) _ = unitStep P.L^_ • (iteratedFDeriv ℝ n R 0) _ at hev
    rw [hev]; unfold a; rw [hu,Tensor.coeff]; simp only [smul_apply]; exact smul_comm ..
  rw [H,map_mul, Algebra.smul_def, mul_assoc]; simp

/-- Also no decrease of slot degree even when weight *increases*.
Use the genuine pre-mask slot representation witnessing `pop`. -/
lemma keeps_degree (hF : Bid.pop T) (i : F.Index) (hm : m ≤ d) (hl : n ≤ d) (hn : n < (F.grades i).2) :
    gradePart (m,n) (rawBook T h (stored P k hk ht) (copy F i))=0 := by
  classical
  let K:=linesOf P k
  let f : Snap G d → Dev T.stencil G := trace T.stencil K
  let g := column T i
  let C := copy F i
  let R := seen T C K
  have hf := (show ContDiff ℝ ω f from trace_smooth (stored P k hk ht) ..).contDiffAt (x:=0)
  have hg : ContDiff ℝ ω g:=column_smooth ..
  have hz : Tensor.coeff R n 0=0 := by
    have he : R=g ∘ f:=rfl
    have ht : iteratedFDeriv ℝ n (g ∘ f) 0=0 := by
      ext v; rw [Cases.compReads hg.contDiffAt hf le_top]; apply Finset.sum_eq_zero; intro c _
      rw [Cases.caseRead, show f 0=0 from trace_root _, show iteratedFDeriv ℝ c.length g 0=_ from radials_vanish T hF _ _ (c.length_le.trans_lt hn)]; rfl
    rw [Tensor.coeff,he,ht,smul_zero]
  let U := seen_safe T h (stored P k hk ht) C
  apply Subtype.ext
  change (gradePart _ (Parts.archive U)).val=0
  rw [Parts.capture U hm hl, show Tensor.coeff R n 0=0 from hz]; simp [WardBin.tile]

omit h hk ht
/-- No extra-order indices slipped in via limiting basis. -/
lemma second_fits (F : Labels.Frame G d) (i : F.Index) : (F.grades i).2 ≤ d := by
  classical
  have hh : (F.basis i).val ≠ 0 := fun h=> F.basis.ne_zero i (Subtype.ext h)
  obtain ⟨b,hb⟩ := (Finset.nonempty_iff_ne_empty.mpr (show (F.basis i).val.support ≠ ∅ by simpa using hh))
  · have he := (pure_grade _ _).mp (F.pure i) (MvPolynomial.mem_support_iff.mp hb)
    have hp := power_le b
    calc
      _ = (Finsupp.weight bidegree b).2 := congr_arg Prod.snd he.symm
      _ ≤ height b := hp
      _ ≤ d := (MvPolynomial.mem_restrictSupport_iff ℂ).mp (F.basis i).property.1 hb

lemma costs_only (F : Labels.Frame G d) (i : F.Index) (x : Label G d) :
    F.coords x i=F.coords (gradePart (F.grades i) x) i := by
  classical
  have hi := F.bound i
  have hh := second_fits F i
  conv_lhs => rw [← Labels.decompose x]
  rw [map_sum,Finset.sum_apply,Finset.sum_eq_single (F.grades i).1]
  · rw [map_sum,Finset.sum_apply,Finset.sum_eq_single (F.grades i).2]
    · intro a _ he; exact F.power_coefficient i (fun H=>he (congr_arg Prod.snd H)) (gradePart_mem ..)
    simp only [Finset.mem_range, Nat.lt_succ_of_le hh]; simp
  · intro a _ he; rw [map_sum,Finset.sum_apply]; exact Finset.sum_eq_zero fun b _ => F.power_coefficient i (fun h=> he (congr_arg Prod.fst h)) (gradePart_mem (a,b) x)
  simp only [Finset.mem_range,Nat.lt_succ_of_le hi]; simp

include h hk ht
lemma imprint (hd : d≤j) (i b : F.Index) (hb : (F.grades b).1≤(F.grades i).1) :
    receipt T h (stored P k hk ht) (copy F i) b=
      if b=i then (((unitStep P.L^((F.grades b).1):ℝ):ℂ)) else 0 := by
  change F.coords _ b= _; rw [costs_only F b, ← show ((F.grades b).1,(F.grades b).2) =(F.grades b) from rfl,
    stamps T h P k hk ht hd i hb (second_fits F b), F.coords.map_smul]
  change _ * F.coords (gradePart (F.grades b) (F.basis i)) b= _
  rw [← costs_only F b (F.basis i),Frame.coords_basis]; simp [Pi.single_apply]

lemma print_later (hF : Bid.pop T) (i b : F.Index) (hb : (F.grades b).2 < (F.grades i).2) :
    receipt T h (stored P k hk ht) (copy F i) b=0 := by
  change F.coords _ b=0; rw [costs_only F b,show gradePart (F.grades b) _ = _ from keeps_degree T h P k hk ht hF i (F.bound b) (second_fits F b) hb]
  simp
end YM.Planned.PrimaryIntegral295.Film
