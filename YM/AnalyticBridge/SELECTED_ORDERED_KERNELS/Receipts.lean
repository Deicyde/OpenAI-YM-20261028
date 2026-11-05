import YM.AnalyticBridge.SELECTED_ORDERED_KERNELS.Issued

/-!
# Fixed-L torus payments in Lie calculus for the physical no-hole families

both forms of pricing (polynomially growing full directions,
or coefficient tensor stars with a fixed position or tagged anywhere). All
rates simultaneously positive through the max order. Retain gain in window
extent and in shift. Post-L/PathData-dependent proofs here are not calendar
quotes for arbitrary analytic consumers of the RG, see docs/Budget.
-/

set_option autoImplicit false
noncomputable section
namespace YM.SelectedOrderedKernels.NoHole
open Lattice Wilson RG Function WardBin.Lies Exterior FreeResolvent Affine Mark TestD Window Stars Tree Precision
open scoped BigOperators Topology Matrix.Norms.Frobenius ContDiff
variable {G : Gauge} {c f : Side} {S : StepData c f} {ι : Type*} [Fintype ι]

def coins (G : Gauge) (P : Patch) (s : ℝ) := max (torusPay (Bloch.Co P.L (PAC G 1)) s) (torusPay (PAC G 1) s)

def release (G : Gauge) (P : Patch) (K : KernelChoices) (p : Clip) (n : ℕ) (M σ : ℝ) :=
    narrow n (width G P K p n M σ) / (2*(n+3:ℕ))

structure Receipt (S : StepData c f) (a : ι → Site c) (k : ℕ) (s V : ℝ) (M N : ℕ → ℝ)
    (F : Forest S.ratio → Config G c → Matrix ι ι ℝ) (field : Config G c := 1) : Prop where
  rate : 0 < s
  paid : Paid S a k s s s M N F field
  tagBill (T U : Forest S.ratio) (v : Site c) : changed S T U v → ∀ j ≤ k, ∀ z : Pins G c j,
    Bill (marked (native c) (marks G c s) v s) (native c) a a (markedSlots (List.ofFn z)) s (V*N j)
      (ordered (F U) field z - ordered (F T) field z)
  star (T : Forest S.ratio) (x : Site c) (j : ℕ) : j ≤ k → ∀ W : ι → ι → Pins G c j → Bool,
    (∀ i q z, W i q z=true → x=a i ∨ x=a q ∨ ∃ b, x=hearth (z b)) →
      NearStar j (native c) a a hearth x W s (crowd j (M j) V) (fun i q z => ordered (F T) field z i q)
  tagStar (T U : Forest S.ratio) (v : Site c) : changed S T U v → ∀ j ≤ k,
    NearStar j (native c) a a hearth v (fun _ _ _ => true) s (crowd j (N j) V) (fun i q z =>
      ordered (F U) field z i q - ordered (F T) field z i q)
  fields (T : Forest S.ratio) (l : List (Directions G c)) : l.length ≤ k → ∀ (o : Site c) (P : ℕ) (fee : ℝ), 0 ≤ fee →
    (∀ B ∈ l, ∀ t, ‖B t‖ ≤ fee*(1+(separation t.1 o:ℝ))^P) → Bill (radial _ (native c) o P) (native c) a a l s
      (fieldFee s P fee V l.length * M l.length) (leftDerivs (F T) l field)
  tagDirections (T U : Forest S.ratio) (v : Site c) : changed S T U v →
    ∀ l : List (Directions G c), l.length ≤ k → ∀ (o : Site c) (P : ℕ) (fee : ℝ), 0 ≤ fee →
    (∀ B ∈ l, ∀ t, ‖B t‖ ≤ fee*(1+(separation t.1 o:ℝ))^P) →
      Bill (marked (native c) (radial _ (native c) o P) v s) (native c) a a (markedSlots l) s
        (V*(fieldFee s P fee V l.length * N l.length)) (leftDerivs (F U) l field-leftDerivs (F T) l field)

variable {a : ι → Site c} {k n : ℕ} {δ γ d s M σ : ℝ} {m h : ℕ → ℝ} {F : Forest S.ratio → Config G c → Matrix ι ι ℝ}

theorem Paid.bought {field : Config G c} {V : ℝ} (p : Paid S a k δ d γ m h F field) (hs : 0 < s) (hd : 2*(k+3:ℕ)*s ≤ δ) (hd' : δ ≤ d) (hg : δ ≤ γ)
    (hV : 0 ≤ V) (hw : (native c).Volume a s V) (he : (native c).Volume (hearth (G:=G) (r:=1)) s V) :
    Receipt S a k s V m h F field := by
  have hδ : s+s ≤ δ := (show s+s ≤ 2*(k+3:ℕ)*s by push_cast; nlinarith [show 0 ≤ (k:ℝ)*s by positivity]).trans hd
  have ht : s ≤ δ := by linarith
  have hl (j) (hj : j ≤ k) : 2*(j+3:ℕ)*s ≤ δ := (by gcongr : 2*(j+3:ℕ)*s ≤ 2*(k+3:ℕ)*s).trans hd
  have hw' : (native c).Volume a (γ-s) V := volume_down hw (by linarith only [hg,hδ])
  refine ⟨hs,⟨fun T => (p.base T).mono ht (ht.trans hg) le_rfl (fun _ _ => le_rfl),fun T U v hv =>
    (p.variation T U v hv).mono ht (ht.trans hg) (ht.trans hd') le_rfl (fun _ _ => le_rfl)⟩,?_,?_,?_,?_,?_⟩
  · intro T U v hv j hj z
    rw [← ordered_sub z ((p.base U).smooth.prod hj) ((p.base T).smooth.prod hj)]
    exact ((p.variation T U v hv).mono ht le_rfl (ht.trans hd') le_rfl (fun _ _ => le_rfl)).bill z hj hw' hw'
  · intro T x j hj W hW
    exact (p.base T).total hj hs.le (hl _ hj) ((hl _ hj).trans hg) hV hW hw hw he
  · intro T U v hv j hj
    have hh := (p.variation T U v hv).total hj hs.le (hl _ hj) ((hl _ hj).trans hd') ((hl _ hj).trans hg) hV hw hw he
    simp_rw [ordered_sub _ ((p.base U).smooth.prod hj) ((p.base T).smooth.prod hj), Matrix.sub_apply] at hh
    exact hh
  · intro T l hl o P fee hfee hB
    exact ((p.base T).fields l hl (P:=P) (o:=o) hB hs hδ hfee he).mono (ht.trans hg) le_rfl
  · intro T U v hv l hl o P fee hfee hB
    rw [← ((p.base U).smooth).takes_sub (p.base T).smooth l hl]
    exact ((p.variation T U v hv).mono le_rfl le_rfl (ht.trans hd') le_rfl (fun _ _ => le_rfl)).fields l hl (P:=P) (o:=o) hB hs hδ hfee hV he hw' hw'

lemma priced (G : Gauge) (P : Patch) (K : KernelChoices) (p : Clip) (n : ℕ) (hs : 0 < σ) (hm : 0 ≤ M) :
    let d := width G P K p n M σ; let s := release G P K p n M σ
    0 < d ∧ 0 < s ∧ 2*(n+3:ℕ)*s ≤ narrow n d := by
  intro d s
  have h : 0 < d := (gauged G P K p n hs hm).pos
  refine ⟨h, div_pos (narrow_pos n h) (by positivity),?_⟩
  rw [mul_comm _ s]; exact (div_mul_cancel₀ _ (by positivity)).le

theorem ready (p : Clip) (hs : 0 < σ) (hm : 0 ≤ M) {e : ι → raw G f} (he : Injective e) (hk : k ≤ n) :
    let d := width G S.patch S.kernel p n M σ; let s := release G S.patch S.kernel p n M σ
    Paid S (home S ∘ e) k (narrow n d) d γ m h F → d ≤ γ → Receipt S (home S ∘ e) k s (coins G S.patch s) m h F := by
  intro d s paid hγ; obtain ⟨(hd : 0 < d), (hpos : 0 < s), hδ⟩ := priced G S.patch S.kernel p n hs hm
  refine paid.bought hpos (le_trans (by gcongr) hδ) (narrow_le n hd.le) ((narrow_le n hd.le).trans hγ)
    ((torusPay_nn _ _ hpos).trans (le_max_left ..)) (((home_volume _ 1 _ hpos).comp he).le (le_max_left ..))
    ((volume c _ _ hpos).le (le_max_right ..))

section collected
variable (t : S.Choices) (p : Clip) {W : PathData G} {u : ℝ}
variable (hs : 0 < σ) (hm : 0 ≤ M) (hW : Sheet W σ M) (he : Bid.Larger (G:=G) S) (hu : 0 ≤ u)
  (hk : k < n)
include hs hm hW he hu hk

omit hs hm hW he hu hk in
private lemma multiple_width {n : ℕ} {a d : ℝ} (ha : 1 ≤ a) (hd : 0 < d) : d ≤ a*(n+1:ℕ)*d :=
  le_mul_of_one_le_left hd.le (one_le_mul_of_one_le_of_one_le ha (by exact_mod_cast Nat.one_le_of_lt (Nat.zero_lt_succ _)))

/-- Absolute estimates in the `Book`/FTt/dirBound forms, for any fixed
principal set, with true ordered derivatives of all orders tested, on the
whole, unpruned choice of derivative/link slots. Choose e=id for the full
torus. Even when e omitted volumes from the sum we charge the same receipts
and get the same rate. Positive j or tag test gives (1+u)⁻². -/
theorem collected [DecidableEq ι] (r : Admit) {e : ι → raw G f} (h' : Injective e) :
    let s := release G S.patch S.kernel p n M σ; let E := earnings G S.patch S.kernel p n M σ; let V := coins G S.patch s
    Receipt S (home S ∘ e) k s V (fun j => surcharge G j * charges j 1 E (drain u))
      (fun j => surcharge G j * (E*drain u*drain u)) (fun T => resolver (fun z => (paddedGram S t p W r T z).submatrix e e) u) := by
  apply ready p hs hm h' hk.le (principalPaid p t hs hm hW he hu hk r h')
  exact multiple_width (by norm_num) (priced G S.patch S.kernel p n hs hm).1

variable {I : raw G f → Type*} [∀ i, Fintype (I i)] [∀ i, DecidableEq (I i)]


end collected
end YM.SelectedOrderedKernels.NoHole
