import YM.Planned.PRIMARY_INTEGRAL_295.Pearl
import YM.Planned.PRIMARY_INTEGRAL_295.RollFilm

/-!
# Upper entries of the primary matrix: streamed log derivatives

Pre-L pricing from the same Cover/Hermitian Link stamp. Use unweighted
homogeneous moment production as input to bidegree calculations, keeping
all fine-site polynomial components (not reading the coarse mode as
coarse constant link). Engine here is the analytic `Flight` one at the
very same k.
-/
set_option autoImplicit false
set_option maxHeartbeats 600000
noncomputable section
namespace YM.Planned.PrimaryIntegral295.Film
open Filter Function Set Lattice Labels RG Wilson Source Source.Drops Precision Bloch Next.Free Place Carrier Next.Foundations
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius
variable {G : Gauge} {j m n d t : ℕ} {F : Labels.Frame G d} {M : Side}
variable (T : SectionData F) {A : Hol G} (h : T.Sound A)
variable (k : ℝ) (hk : 0 < k) (hj : 4 ≤ j) (ht : 4 ≤ t)

lemma ping_unscaled (S : Finset Cover) (n : ℕ) : ∃ u : ℝ,1≤u ∧ ∀ v : Tensor.T E4 (Axis→G.Color) n,
    ‖ping S (Tensor.diagonal v)‖ ≤ u*‖v‖ := by
  classical
  let g (p : Spot S) := ‖seat (first p).val‖^n
  have he p : 0≤g p := by unfold g; positivity
  let u:= 1+∑ i,g i
  have hv : 1≤u := le_add_of_nonneg_right (Finset.sum_nonneg fun i _=> he i)
  refine ⟨u,hv,fun v => (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun p=>?_⟩
  have hp : ‖Tensor.diagonal v (seat (first p).val)‖≤‖v‖*g p := by simpa [g,Tensor.diagonal] using v.le_opNorm fun _=> seat (first p).val
  have hz : g p ≤ u := (Finset.single_le_sum (fun i _=> he i) (Finset.mem_univ p)).trans (le_add_of_nonneg_left zero_le_one)
  exact (norm_le_pi_norm (Tensor.diagonal v (seat (first p).val)) (beam p)).trans (hp.trans ((mul_le_mul_of_nonneg_left hz (norm_nonneg _)).trans_eq (mul_comm ..)))

include hk hj ht

lemma condition (hd : d≤j) (w : Fin n → ℕ) (X : Fin n → Snap G d) (hp : ∀ i,0<w i) (hX : ∀ i,throughSlot (X i) (w i))
    (he : ∑ i,w i ≤ d) :
    let m := ∑ i,w i
    ∃ D : ℝ,0≤D ∧ ∀ P : Flight j t, ∃ f : Fin m → Potential G,
      iteratedFDeriv ℝ n (trace T.stencil (linesOf P k) (G:=G) (d:=d)) 0 X = ∑ i, ping T.stencil (f i) ∧
      ∀ i : Fin m, f i∈rangeLt (Axis→G.Color) (i.val+1) ∧
        ‖ping T.stencil (f i)‖ ≤ D*unitStep P.L^(i.val+1) := by
  classical
  intro m; let S:=T.stencil
  let f : Potential G := fun x i => iteratedFDeriv ℝ n (lane (G:=G) (d:=d) x i) 0 X
  have hf := (show f∈rangeLt (Axis→G.Color) m from lane_polynomial w X hX hp)
  obtain ⟨q,hq,hf'⟩ := analyze f hf
  obtain ⟨C,hC,H⟩ := deliver (E:=G.Color) k hk hj ht m (he.trans hd)
  choose! u hu hz using fun i:Fin m=>ping_unscaled (G:=G) S i.val
  have hc i := zero_le_one.trans (hu i)
  let U := ∑ i,u i
  have hU : 0≤U := Finset.sum_nonneg fun i _=>hc i
  refine ⟨U*C*pile q,mul_nonneg (mul_nonneg hU (zero_le_one.trans hC)) (pile_pos q),fun P=>?_⟩
  obtain ⟨g,hp',hy,ha,hb⟩ := H P q
  refine ⟨fun i=> Tensor.diagonal (g i),?_,fun i=>⟨exact_le_band (Nat.lt_succ_self _) (Place.simple _),?_⟩⟩
  · ext1 i; rw [trace_mail (stored P k hk ht) ((Cases.arity hp).trans he)];
    change applyLine (linesOf P k) (verdict f) _ _ = _
    rw [← hf',ha,← map_sum]; rfl
  refine (hz i _).trans ?_
  apply (mul_le_mul (Finset.single_le_sum (fun i _ => hc i) (Finset.mem_univ i)) (hb i) (norm_nonneg _) hU).trans_eq
  unfold U; ring

include h
omit hk hj ht in
private lemma bill_all {L : Side} (i : F.Index) (w : Fin n→ℕ) (D : Fin n→ℝ) (u : ∀ j: Fin n, Fin (w j)→Potential G)
    (hD : ∀ j,0≤D j) (hU : ∀ j a, u j a∈rangeLt (Axis→G.Color) (a.val+1))
    (hx : ∀ j (a : Fin (w j)), ‖ping T.stencil (u j a)‖ ≤ D j*unitStep L^(a.val+1)) :
    let Z := iteratedFDeriv ℝ n (column T i) 0
    ‖Z (fun j => ∑ l,ping T.stencil (u j l))‖ ≤
      (Fintype.card (∀ j,Fin (w j)):ℝ) * ‖Z‖ * (∏ j, D j) * unitStep L^((F.grades i).1) := by
  classical
  intro Z
  let C:=‖Z‖*(∏ j,D j); let e:=unitStep L; have he : 0 < e:=unitStep_pos _
  have hc : 0≤C := mul_nonneg (norm_nonneg _) (Finset.prod_nonneg (fun j _=>hD j))
  rw [Z.map_sum (fun j l=>ping T.stencil (u j l))]; refine (norm_sum_le ..).trans ?_
  have H (b : ∀ j,Fin (w j)) : ‖Z (fun j => ping T.stencil (u j (b j)))‖ ≤ C*e^(F.grades i).1 := by
    let p j := (b j).val+1
    by_cases hH : ∑ j,p j < (F.grades i).1
    · rw [show Z (fun _ => _) = 0 from lower A T h i p hH (fun j=> u j (b j)) (fun j=>hU _ _), norm_zero]; positivity
    apply (Z.le_opNorm _).trans
    apply (mul_le_mul_of_nonneg_left (Finset.prod_le_prod (fun j _=>norm_nonneg _) (fun j _=>hx j (b j))) (norm_nonneg _)).trans
    simp only [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, ← mul_assoc]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one he.le (unitStep_le L) (le_of_not_gt hH)) hc
  apply (Finset.sum_le_sum (fun i _=> H i)).trans_eq; simp only [Finset.sum_const,nsmul_eq_mul,Finset.card_univ]; unfold C e; ring

/-- Bounds for every entry *before* removing the overall diagonal. -/
lemma upper_end (hd : d≤j) (i : F.Index) (z : Fin n → WardBin.Board G d) (hZ : WardBin.depth z ≤ d) :
    ∃ D : ℝ,0≤D ∧ ∀ P : Flight j t,
      ‖Tensor.coeff (seen T (copy F i) (linesOf P k)) n 0 (WardBin.chip ∘ z)‖ ≤ D*unitStep P.L^((F.grades i).1) := by
  classical
  let m:= (F.grades i).1
  let V:=WardBin.chip ∘ z
  let w (j : Fin n) := Labels.generation (WardBin.key (z j))
  have he : ∑ i,w i ≤ d := hZ
  let L (P: Flight j t) := trace T.stencil (linesOf P k) (G:=G) (d:=d)
  let B:=column T i
  have H (c : OrderedFinpartition n) :
      ∃ D : ℝ,0≤D ∧ ∀ P:Flight j t, ‖Cases.caseRead c B (L P) 0 V‖ ≤ D*unitStep P.L^m := by
    let f:=Cases.costs c w
    have hh j : throughSlot (V j) (w j) := fun a ha =>
      Pi.single_eq_of_ne (show a ≠ (z j).1 from fun h=> (Nat.lt_irrefl _) (h ▸ ha)) _
    have hp i : 0<w i := (by unfold w Labels.generation; omega)
    have hF j : f j ≤ d := (Finset.single_le_sum (f:=f) (fun i _ => Nat.zero_le _) (Finset.mem_univ j)).trans ((Cases.all c w).trans_le he)
    choose! D hD H using fun j => condition T k hk hj ht hd (w ∘ c.emb j) (V ∘ c.emb j)
      (fun s=> hp _) (fun s=>hh _) (hF j)
    let d := (Fintype.card (∀ j,Fin (f j)):ℝ) * ‖iteratedFDeriv ℝ c.length B 0‖ * (∏ j,D j)
    have hb' := Finset.prod_nonneg (s:=Finset.univ) (fun i _=>hD i)
    refine ⟨d,mul_nonneg (by positivity) hb', fun P=>?_⟩
    choose g h1 h2 using fun i=> H i P
    unfold Cases.caseRead; rw [show L P 0=0 from trace_root _, show
      (fun i=> iteratedFDeriv ℝ _ (L P) 0 (V ∘ c.emb i))=(fun i=> ∑ l,ping T.stencil (g i l)) from funext h1];
    exact bill_all T h i f D g hD (fun j l=>(h2 j l).1) (fun j l=>(h2 j l).2)
  choose D hD H using H
  let u := ‖((n.factorial:ℝ)⁻¹)‖
  have hc := Finset.sum_nonneg (s:=Finset.univ) (fun i _=>hD i)
  refine ⟨u*∑ i,D i,mul_nonneg (norm_nonneg _) hc,fun P=>?_⟩
  unfold Tensor.coeff; simp only [smul_apply,norm_smul]
  rw [show seen T _ _= B ∘ L P from rfl]
  rw [Cases.compReads (column_smooth T i).contDiffAt ((trace_smooth (stored P k hk ht) T.stencil d).contDiffAt) le_top] -- maybe unfold B
  rw [mul_assoc u]; apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  rw [Finset.sum_mul]; exact (norm_sum_le ..).trans (Finset.sum_le_sum (fun i _=>H i P))
end YM.Planned.PrimaryIntegral295.Film
