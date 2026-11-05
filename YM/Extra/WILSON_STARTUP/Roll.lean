import YM.Extra.WILSON_STARTUP.Reflect
import YM.Work.F08.Mixed

/-!
# Matching the local boundary Bed by isometric change of mf on the first step

One-time, widths re-quoted from pre-L prices and stage choices. NO accumulated
cost each depth. Arbitrary pre-existing top roots (can rotate the linear curl),
all S periods still exact on zero and nonzero modes. Not applied to fields in
the nonlinear sector! New mf will have to be used in any such estimates using
the Towers; this doesn't preserve mf-based step predicates automatically.
-/
noncomputable section
set_option autoImplicit false
namespace YM.WilsonStartup.Change
open Matrix Function Filter RG Wilson Lattice Bid Precision Exterior Bloch Tree Work Design Polar F08
open scoped BigOperators Matrix.Norms.Frobenius Classical
variable {G : Gauge} {a : Levels G} {M H : Horizon a} {K : MapPrices}
variable {n f L : Side} {S : StepData n f} {B C : Bed} {p q : Clip} {η Ω : ℝ} {U : Towers L}

def spin (S : LiftRows) (U : Towers L) := { U with mf := fineCompose S U.mf }

lemma trans_roll {S : StepData n f} {X : LiftRows} {U : Towers S.patch.L} (hU : Towers.Roll S B C U p q)
    (hx : installed S.ratio (spin X U).mf = X.acts f * installed S.ratio U.mf)
    (hg : (X.acts f)ᵀ * X.acts f = 1)
    (h : X.acts f * (B.full p f * d 1 f) = (bed p).full p f * d 1 f) : Towers.Roll S (bed p) C (spin X U) p q := by
  refine ⟨?_,hU.n,?_,hU.nPart,hU.oPart,?_⟩
  · rw [hx,Matrix.transpose_mul,← Matrix.mul_assoc,Matrix.mul_assoc ((installed _ _)ᵀ),hg,Matrix.mul_one]; exact hU.m
  · rw [hx, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc (installed _ _), hU.fPart, ← Matrix.mul_assoc,h]; rfl
  rw [hx,← h,Matrix.transpose_mul,Matrix.mul_assoc,← Matrix.mul_assoc ((X.acts f)ᵀ),hg,Matrix.one_mul]; exact hU.orthogonal

lemma isometry (p : Clip) {A η : ℝ} (hη : 0 < η) : ∃ τ C : ℝ, 0 < τ ∧ ∀ B : Bed, p.direct ≤ 1 → B.roots.strip η A → ∃ X : LiftRows,
    X.strip τ C ∧ ∀ n : Side, (X.acts n)ᵀ*X.acts n=1 ∧ ∀ a v, Floor B p n a v → B.diagonal.acts n=1 →
        X.acts n * (B.full p n*d 1 n) = (bed p).full p n*d 1 n := by
  let D := max 1 A
  have hD : 1 ≤ D := le_max_left ..
  obtain ⟨τ,Z,ht,hZ,h⟩ := orient_uniform p (zero_le_one.trans hD) hη
  refine ⟨τ,(Fintype.card Layers2:ℝ)*(Z*Z),ht,fun B hv hB => ?_⟩
  obtain ⟨X,hX,hx⟩ := h B (strip_mono hB le_rfl (le_max_right ..))
  obtain ⟨Y,hY,hy⟩ := h (bed p) ((Design.covered p hv hD).2.2.2.1)
  refine ⟨composeRows (transRows Y) X, strip_compose ht.le (strip_trans hY) hX,fun n => ?_⟩
  rw [acts_compose ht.le (strip_trans hY) hX, acts_trans]
  have hu := _root_.mul_eq_one_comm.mp (hy n).1
  refine ⟨?_,fun a v hf hh => ?_⟩
  · rw [transpose_mul,transpose_transpose,← Matrix.mul_assoc,Matrix.mul_assoc ((X.acts n)ᵀ),hu, Matrix.mul_one]; exact (hx n).1
  rw [Matrix.mul_assoc,(hx n).2 a v hf hh,← (hy n).2 1 1 (Design.level p hv n le_rfl le_rfl) (by simp [bed,spike_acts]),
    ← Matrix.mul_assoc,(hy n).1,Matrix.one_mul]

lemma deep_mono (U : Towers L) {η τ A Ω : ℝ} {k : ℕ} (h : U.Deep η A k) (hη : τ ≤ η) (hA : A ≤ Ω) : U.Deep τ Ω k :=
  ⟨strip_mono h.1 hη hA,strip_mono h.2.1 hη hA,strip_mono h.2.2.1 hη (by gcongr), fun a ha =>
    ⟨strip_mono ((h.2.2.2 a ha).1) hη (by gcongr),strip_mono ((h.2.2.2 a ha).2) hη (by gcongr)⟩⟩

lemma spin_cost (p : Clip) (η A : ℝ) (hη : 0 < η) : ∃ τ C : ℝ, 0 < τ ∧
    ∀ B : Bed, p.direct ≤ 1 → B.roots.strip η A → ∃ X : LiftRows, ∀ L k (U : Towers L), U.Deep η A k →
      (spin X U).Deep τ C k ∧ ∀ c f h,
        installed (Ratio.mk (c:=c) (f:=f) L h) (spin X U).mf = X.acts f * installed ⟨L,h⟩ U.mf ∧
        ((X.acts f)ᵀ*X.acts f=1 ∧ ∀ a v, Floor B p f a v → B.diagonal.acts f=1 → X.acts f*(B.full p f * d 1 f)=(bed p).full p f * d 1 f) := by
  obtain ⟨t,C,ht,h⟩ := isometry p (A:=A) hη
  let τ := min t η
  have hτ : 0 < τ := lt_min ht hη
  let b : ℝ := Fintype.card Layers2 * C * A
  let Z := max b A
  refine ⟨τ,Z,hτ,fun B hv hB => ?_⟩
  obtain ⟨X,hX,hx⟩ := h B hv hB
  refine ⟨X,fun L k U hU => ?_⟩
  have he := deep_mono U hU (min_le_right .. : τ≤η) le_rfl
  have hP := strip_mono hX (min_le_left .. : τ≤t) le_rfl
  have hs := strip_fine hτ.le hP he.2.2.1
  have hm := deep_mono U he le_rfl (le_max_right .. : A ≤ Z)
  refine ⟨⟨hm.1,hm.2.1,strip_mono hs le_rfl ?_,hm.2.2.2⟩,fun c f h' => ⟨installed_fine (g:=Ratio.mk ..) hτ.le hP he.2.2.1, hx _⟩⟩
  rw [show _ * (C * (A / (L.val:ℝ)^2)) = b/(L.val:ℝ)^2 by unfold b; ring]
  exact div_le_div_of_nonneg_right (le_max_left ..) (by positivity)

lemma floor_mono {a b c d : ℝ} (h : Floor B p n a b) (hc : c ≤ a) (hd : b ≤ d) : Floor B p n c d := by
  have he (P : FormBlock n) (h : Numeric P a b) : Numeric P c d := fun v =>
    have ht : 0 ≤ v ⬝ᵥ v := Finset.sum_nonneg fun _ _ => mul_self_nonneg _
    ⟨(mul_le_mul_of_nonneg_right hc ht).trans (h v).1, (h v).2.trans (mul_le_mul_of_nonneg_right hd ht)⟩
  exact { h with uniform := ⟨he _ h.uniform.1,he _ h.uniform.2⟩ }

lemma covered_mono {a b c d : ℝ} (h : B.covered a b) (hc : c ≤ a) (hd : b ≤ d) : B.covered c d :=
  ⟨strip_mono h.1 hc hd, strip_mono h.2.1 hc hd, strip_mono h.2.2.1 hc hd,strip_mono h.2.2.2.1 hc hd, strip_mono h.2.2.2.2 hc hd⟩

theorem retarget (C : Supply.Sheet G) (K : MapPrices) : ∃ K' : MapPrices, ∀ (a : Levels G), a.clock.stage=C.profile →
    (∀ N,(a.params N).clip.direct ≤ 1) → ∀ M : Horizon a, M.Suffices K → ∃ H : Horizon a, H.Suffices K' ∧ Overlay H M := by
  choose t v ht hf using fun i => spin_cost (C.profile i).clip (K.α i) (K.Ω i) (K.alpha_pos i)
  let K' : MapPrices := {
    α := fun i => min (K.α i) (t i)
    alpha_pos := fun i => lt_min (K.alpha_pos i) (ht i)
    Ω := fun i => max 1 (max (K.Ω i) (v i))
    η := fun i => min 1 (K.η i)
    eta_pos := fun i => lt_min one_pos (K.eta_pos i) }
  refine ⟨K', fun a ha hg M hM => ?_⟩
  let H := mapped M
  have h := overlaid M
  have ha' (N : ℕ) : C.profile (a.clock.J N) = a.params N := congr_fun ha.symm _
  choose X hX using fun N : ℕ => hf (a.clock.J N) (M.H N N) (by rw [ha']; exact hg N) ((hM.rows N N le_rfl).2.2.2.1)
  let T := fun (N m : ℕ) => if m+1=N then spin (X (m+1)) (M.towers N m) else M.towers N m
  have hT N m : (T N m).A0=(M.towers N m).A0 ∧ (T N m).T=(M.towers N m).T := by unfold T; split <;> exact ⟨rfl,rfl⟩
  have hm i : K.Ω i ≤ K'.Ω i := (le_max_left ..).trans (le_max_right ..)
  have he i : v i ≤ K'.Ω i := (le_max_right ..).trans (le_max_right ..)
  refine ⟨⟨H.H,T⟩,⟨fun N m hx => ?_,fun N m hx n => ?_,fun N m hx => ?_,fun N m p hx => ?_,fun N m p hx => ?_,fun N n => ?_⟩,
    ⟨h.peak,h.other,fun N m _ => (hT N m).1⟩⟩
  · obtain hx|rfl := lt_or_eq_of_le hx
    · dsimp only; rw [h.other N m hx]; exact covered_mono (hM.rows _ _ hx.le) (min_le_left ..) (hm _)
    dsimp only; rw [h.peak]; exact Design.covered _ (hg m) (le_max_left ..)
  · dsimp only; obtain hx|rfl := lt_or_eq_of_le hx
    · rw [h.other N m hx]; exact floor_mono (hM.all _ _ hx.le n) (min_le_right ..) (hm _)
    rw [h.peak]; exact Design.level _ (hg m) _ (min_le_left ..) (le_max_left ..)
  · change (T N m).Deep _ _ _
    unfold T; obtain hq|rfl := lt_or_eq_of_le (a:=m+1) (b:=N) hx
    · rw [if_neg hq.ne]; exact deep_mono _ (hM.costs N m hx) (min_le_left ..) (hm _)
    rw [if_pos rfl]; exact deep_mono _ (hX (m+1) _ _ _ (hM.costs _ _ hx) |>.1) (min_le_right ..) (he _)
  · dsimp only; rw [h.other _ _ hx]
    have hu : Towers.Diagonal (a.clock.op m p) (M.H N (m+1)) (M.H N m) (T N m) := by
      obtain ⟨e1,e2,e3⟩ := hM.crossings N m p hx
      constructor <;> simpa only [(hT N m).1,(hT N m).2]
    obtain hq|rfl := lt_or_eq_of_le (a:=m+1) (b:=N) hx
    · rw [h.other _ _ hq]; exact hu
    rw [h.peak]; exact top_diagonal hu (hM.all _ _ hx _) (hM.top _ _)
  · dsimp only; rw [h.other _ _ hx]; unfold T; obtain hq|rfl := lt_or_eq_of_le (a:=m+1) (b:=N) hx
    · rw [if_neg hq.ne,h.other _ _ hq]; exact hM.stack _ _ _ hx
    rw [if_pos rfl,h.peak]
    obtain ⟨hL,hR,h⟩ := (hX (m+1) _ _ _ (hM.costs _ _ hx)).2 _ _ (a.clock.op m p).sizes
    rw [ha'] at h
    exact trans_roll (hM.stack _ _ _ hx) hL hR (h _ _ (hM.all _ _ hx _) (hM.top _ _))
  change (H.H N N).diagonal.acts n = 1
  rw [overlaid M |>.peak]; simp only [bed,spike_acts,one_smul]
end YM.WilsonStartup.Change
