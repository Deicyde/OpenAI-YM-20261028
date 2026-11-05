import YM.Push.LOOP_COEFFICIENT.Cofinal

/-!
# Pullback of fine pair symbols on actual aliases

Raw polarizations per input/output wave (not normalized Fourier columns).
The per-fine-site precision therefore acquires the block volume L^4.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.Loops
open Matrix Function Filter Set Bloch Lattice Laurent
open scoped Topology BigOperators
variable {c f n : Side} {g : Ratio c f}

def collapse (g : Ratio c f) : Site f →+ Site c :=
  { toFun := fun x i => ZMod.castHom (by rw [g.exact_size]; exact Nat.dvd_mul_right ..) (Per c) (x i)
    map_add' x y := funext fun i => (ZMod.castHom _ (Per c)).map_add (x i) (y i)
    map_zero' := by ext; simp }
lemma collapse_wrap (g : Ratio c f) (z : Cover) : collapse g (wrap f z) = wrap c z := by ext i; exact map_intCast (ZMod.castHom (show c.val ∣ f.val by simp [g.exact_size]) (Per c)) (z i)
@[simp] lemma collapse_alias (g : Ratio c f) (z : Cover) (l : Site g.count) : collapse g (aliasSite g z l) = wrap c z := by
  rw [aliasSite,collapse_wrap,map_add,map_nsmul,
    show c.val • wrap c (lift l) = 0 by ext i; change (c.val • wrap c (lift l) i : Per c) = 0; simp [Per]]; simp

variable {E F a b : Type} [Fintype E] [Fintype F] [Fintype a] [Fintype b] [DecidableEq a] [DecidableEq b]
    {M : Grid f E a} {N : Grid c F b} {A : Matrix E F ℂ}

abbrev Profiles (L : Side) (a b : Type) := Momentum → Site L → Matrix a b ℂ

def Projects (g : Ratio c f) (M : Grid f E a) (N : Grid c F b) (A : Matrix E F ℂ) (V : Profiles g.count a b) :=
    ∀ z : Cover, A * plane N (wrap c z) = ∑ l : Site g.count,plane M (aliasSite g z l) * V (quant c z) l

def collectPair {L : Side} (V : Profiles L a b) (U : Momentum → Matrix a a ℂ) (p : Momentum) :=
    (L.val:ℂ)^4 • ∑ k : Site L,(V (-p) (-k)).transpose * U (aliasAt p k) * V p k

variable {V : Profiles g.count a b} {X : Matrix E E ℂ}

def MeshClosed (M : Grid f E a) (X : Matrix E E ℂ) := ∀ k i : Site f, k+i≠0 → sample M M X k i = 0

omit [Fintype b] in
lemma pullPair_expansion (h : Projects g M N A V) (X : Matrix E E ℂ) (w z : Cover) :
    sample N N (A.transpose * X * A) (wrap c w) (wrap c z) = (g.count.val:ℂ)^4 • ∑ i, ∑ j,
      (V (quant c w) i).transpose * sample M M X (aliasSite g w i) (aliasSite g z j) * V (quant c z) j := by
  have he : (g.count.val:ℂ)^4 * ((f.val:ℂ)^4)⁻¹ = ((c.val:ℂ)^4)⁻¹ := by
    rw [g.exact_size,Nat.cast_mul]; field_simp [side_ne]
  unfold sample
  rw [← Matrix.mul_assoc _ _ A,← Matrix.mul_assoc _ A.transpose,← transpose_mul,Matrix.mul_assoc _ A, h,h, transpose_sum,Matrix.sum_mul]
  simp only [Matrix.sum_mul,Matrix.mul_sum,transpose_mul, Finset.smul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Matrix.mul_smul,Matrix.smul_mul, smul_smul,he]; simp only [Matrix.mul_assoc]

omit [Fintype b] in
lemma pullPair_closed (h : Projects g M N A V) (hc : MeshClosed M X) : MeshClosed N (A.transpose * X * A) := by
  intro i j h1
  conv_lhs => rw [← wrap_lift i, ← wrap_lift j, pullPair_expansion h]
  simp only [show ∀ a b, sample M M X (aliasSite g (lift i) a) (aliasSite g (lift j) b) = 0 from fun a b => hc _ _ (by
    intro he
    have hh := congr_arg (collapse g) he
    simp only [map_add, collapse_alias, wrap_lift,map_zero] at hh; exact h1 hh),Matrix.mul_zero,Matrix.zero_mul,Finset.sum_const_zero, smul_zero]

omit [Fintype b] in
lemma pullPair_sample (h : Projects g M N A V) (hc : MeshClosed M X) (z : Cover) :
    sample N N (A.transpose * X * A) (-wrap c z) (wrap c z) = (g.count.val:ℂ)^4 • ∑ i,
      (V (-quant c z) (-i)).transpose * sample M M X (-aliasSite g z i) (aliasSite g z i) * V (quant c z) i := by
  rw [← map_neg,pullPair_expansion h,Finset.sum_comm]
  simp only [quant_neg]
  congr 1; refine Finset.sum_congr rfl fun i _ => ?_
  rw [Fintype.sum_eq_single (-i),aliasSite_neg]
  intro k hk; rw [hc _ _ (fun h => hk <| aliasSite_inj (-z) ((eq_neg_of_add_eq_zero_left h).trans (aliasSite_neg ..))),Matrix.mul_zero,Matrix.zero_mul]

omit [Fintype b] in
lemma Projects.exact {U} (h : Projects g M N A V) (hc : Compares M M X U 0) :
    Compares N N (A.transpose * X * A) (collectPair V U) 0 := ⟨pullPair_closed h hc.off,fun ⟨z,h1,h2⟩ u v => by
      subst_vars
      rw [pullPair_sample h hc.off]; simp only [hc.exact_sample (alias_match g z _),collectPair,sub_self,norm_zero,le_rfl]⟩

section sequence
variable {s s' : ℕ → Side} {E F : ℕ → Type} [∀ i, Fintype (E i)] [∀ i, Fintype (F i)] {M : ∀ i, Grid (s' i) (E i) a} {N : ∀ i, Grid (s i) (F i) b}
    {L : Side} {X : ∀ i, Matrix (E i) (E i) ℂ} {A : ∀ i, Matrix (E i) (F i) ℂ} {V : Profiles L a b} {U : Momentum → Matrix a a ℂ}

lemma tends_mul {a b c : Type} [Fintype b] {f : ℕ → Matrix a b ℂ} {g : ℕ → Matrix b c ℂ} {F G} (hf : Tendsto f atTop (𝓝 F))
    (hg : Tendsto g atTop (𝓝 G)) : Tendsto (fun i => f i * g i) atTop (𝓝 (F * G)) := by
  refine tendsto_pi_nhds.mpr fun i => tendsto_pi_nhds.mpr fun j => ?_
  exact tendsto_finsetSum _ fun k _ => (tendsto_pi_nhds.mp (tendsto_pi_nhds.mp hf i) k).mul (tendsto_pi_nhds.mp (tendsto_pi_nhds.mp hg k) j)

omit [Fintype b] in
lemma mirrors_pull (hg : ∀ i, (s' i).val = (s i).val * L.val) (hA : ∀ i, Projects (Ratio.mk _ (hg i)) (M i) (N i) (A i) V)
    (hc : ∀ i, MeshClosed (M i) (X i)) (h : Mirrors M M X U)
    (hV : ∀ p, star p=p → ∀ k, ContinuousAt (fun p => V p k) p) : Mirrors N N (fun i => (A i).transpose * X i * A i) (collectPair V U) := by
  intro p f k hp hf hk
  choose z hz hz' using hk
  let R i := Ratio.mk _ (hg i)
  have he i l : Matches (aliasAt (f i) l) (aliasSite (R i) (z i) l) := hz i ▸ alias_match (R i) (z i) l
  have hT (l : Site L) : Tendsto (fun i => sample (M i) (M i) (X i) (-aliasSite (R i) (z i) l) (aliasSite (R i) (z i) l)) atTop (𝓝 (U (aliasAt p l))) :=
    h (aliasAt p l) _ _ (by rw [← alias_conj,hp]) ((hf.const_smul _).add tendsto_const_nhds) (fun i => he i l)
  have hW (l : Site L) := ((continuous_pi fun i => continuous_pi fun j =>
    (show Continuous fun x : Matrix a b ℂ => x j i from (continuous_apply i).comp (continuous_apply j))).tendsto
    (V (-p) l)).comp ((hV (-p) (by rw [star_neg,hp]) l).tendsto.comp hf.neg)
  have hx := tendsto_const_nhds (x:=((L.val:ℂ)^4)) |>.smul (tendsto_finsetSum Finset.univ (fun l _ =>
    tends_mul (tends_mul (f:=fun i => (V (-f i) (-l)).transpose) (hW (-l)) (hT l)) ((hV p hp l).tendsto.comp hf)))
  exact hx.congr fun i => by simp_rw [Function.comp_apply,hz' i,hz i, pullPair_sample (hA i) (hc i)]; rfl
end sequence
end YM.Push.Loops
