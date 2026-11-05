import YM.RG08.Packets.Harmonic
import YM.RG08.Rate.Events
import YM.Next.FREE_KERNELS.Rack

/-!
# Canonical flat overlap flow

No appeal to continuum/qualitative convergence (from which
a rate wouldn't follow).
-/
noncomputable section
namespace YM.RG08.Flat
open Filter Finset Pert.Bulk Laurent Lattice Bloch Stationary Function Matrix RG08.Packets RG08.Rate RG Precision Next.Free Exterior
open scoped Topology ENNReal

set_option autoImplicit false
universe u

variable {G : Gauge} {a : Levels G}

def bridgeWidth (a : Levels G) (P : MapPrices) (m : ℕ) := min 1 (min (P.α (a.clock.J (m+1))) (P.α (a.clock.J m)))
def header (a : Levels G) (P : MapPrices) (m : ℕ) := allotment P (a.clock.J (m+1)) (a.clock.J m)
def quote (a : Levels G) (P : MapPrices) (i : ℕ) (u : ℝ) := neutralCoin (a.S.block i) Faces Faces u (header a P i) (header a P i)
def topTab (a : Levels G) (P : MapPrices) (m : ℕ) : ℝ := Fintype.card Faces * (P.Ω (a.clock.J m)+ P.Ω (a.clock.J m))

variable {H : Horizon a} {P : MapPrices}

theorem Ω_pos (h : H.Suffices P) (m : ℕ) : 0 ≤ P.Ω (a.clock.J m) := merit (h.rows m m le_rfl)

theorem quote_pos (h : H.Suffices P) (i : ℕ) {u:ℝ}(hu:0≤u) : 0 ≤ quote a P i u := by
  have ht := Ω_pos h i; have hv := Ω_pos h (i+1)
  unfold quote header allotment Pert.Bulk.pre neutralCoin; positivity

/-- All torus sides of the actual schedule at this level. One cover curvature kernel. The
Sigil can be tested even when the curl precision has a harmonic zero (never invert it). -/
structure FlatRep (H : Horizon a) (N n i : ℕ) (σ p : ℝ) (K : Packet 1 Faces) : Prop where
  declared : Folded σ K p
  smooth : neutral K
  covariant : town 1 K
  here t : let c := a.S.side i t; Sigil K c (quadratic (H.H n i) c-quadratic (H.H N i) c)

private theorem at_end (h : H.Suffices P) (N n : ℕ) (hm : N ≤ n) {σ : ℝ} (hs : 0 < σ) (ha : σ ≤ P.α (a.clock.J N)) :
    ∃ K : Packet 1 Faces, FlatRep H N n N σ (topTab a P N) K := by
  let Y:=H.H n N
  let Z:=H.H N N
  have hY := h.rows n N hm
  have hZ := h.rows N N le_rfl
  have he := Ω_pos h N
  let K : Packet 1 Faces := fun x y=> saddle Y.metric x y-saddle Z.metric x y
  have ht (c:Side) := turn_class (Y:=Y) (H:=Z) (h.all n N hm c) (h.all N N le_rfl c) (p:=P.Ω (a.clock.J N)) (q:=P.Ω (a.clock.J N)) (σ:=σ) (fun i j=>(hY.2.1 i j).mono ha le_rfl) (fun i j=>(hZ.2.1 i j).mono ha le_rfl) hs.le he he
  exact ⟨K,(ht 1).2.2.1, (ht 1).1,(ht 1).2.1,fun t=> (ht (a.S.side N t)).2.2.2⟩

/-- `duo` condition for reproduction on the **previous** history. -/
private theorem to_here (h : H.Suffices P) {N n i : ℕ}(hm : N ≤ n) (hi : i < N)
    (hD : (H.towers N i).T=((destination a N i).duo a.clock.kernel.penalty).T)
    (σ u p : ℝ) (hu : 0 < u) (hσ:0<σ) (hg : σ ≤ bridgeWidth a P i) (hv : 2*σ ≤ (a.S.block i).val * u) (hp : 0 ≤ p)
    (K : Packet 1 Faces) (hK : FlatRep H N n (i+1) u p K) :
    let B' := push K (fine_share H n i) (fun _ _=> fine_share H N i)
    FlatRep H N n i σ (quote a P i u * p) B' := by
  let j := a.clock.J (i+1); let j' := a.clock.J i
  let T := fine_share H N i
  have hω := P.alpha_pos j; have hω' := P.alpha_pos j'
  have ht:= Ω_pos h (i+1)
  have hY := (h.rows N (i+1) hi).2.2.1
  have hZ := (h.rows N i hi.le).2.1
  have h' := (h.costs N i hi).2.2.2 [] (Nat.zero_le _)|>.2
  have hd : (H.towers N i).T.strip (P.α j) (P.Ω j):= by
    have hl : 1 ≤ (a.S.block i).val := (a.S.block i).pos
    intro x v
    exact (h' x v).mono le_rfl (div_le_self ht (one_le_pow₀ (by exact_mod_cast hl)))
  have HR : travels T := travels_route (destination a N i) a.clock.kernel (a.clock.adm _) hD hd hY hZ hω.le hω'.le ht
  intro B'
  have hI : i < n := lt_of_lt_of_le hi hm
  have he (t:ℕ) : neutral B' ∧ town 1 B' ∧ Folded σ B' (quote a P i u * p) ∧
      Sigil B' (a.S.side i t) (quadratic (H.H n i) (a.S.side i t)-quadratic (H.H N i) (a.S.side i t)) :=
    toward _ _ _ _ _ _ _ (h.crossings N i t hi) (h.crossings n i t hI)
      (h.all N (i+1) hi _) (h.all N i hi.le _) (h.all n (i+1) hI _) (h.all n i hI.le _)
      (fine_share H n i) (fine_share H N i) (atlas_here h 1 hI) (atlas_here h 1 hi)
      (pass_response _ _ _) (pass_response _ _ _) (values h hI t) (values h hi t) hK.smooth hK.covariant hK.declared hu hσ.le hg hv hp (hK.here t) HR
  exact ⟨(he 0).2.2.1,(he 0).1,(he 0).2.1,fun t=>(he t).2.2.2⟩

structure World (X : Type u) (G : Gauge) where
  trial (x:X) : Levels G
  low (x:X) : ℕ
  fine (x:X) : ℕ
  extra (x:X) : ℕ -- n≥N
  measure (x:X) : ℕ
  Z (x:X) : ℝ
  Z_nonneg x : 0 ≤ Z x
  deep x : low x ≤ fine x
  earlier x : fine x ≤ extra x

namespace World
variable {X : Type u} {W : World X G} {P : MapPrices} (H : (x:X) → Horizon (W.trial x))

def bar (W : World X G) : Stair X := ⟨fun x=> (W.trial x).S,W.low,W.fine,W.measure,W.Z,W.Z_nonneg⟩

/-- Additional numerical inputs *after* setting P and the finite width curve in smoothing index.
In particular do not set floor with an estimate computed only after L. Apply on smoothing schedules
chosen to meet these conditions (and all the other finite demands). -/
structure Funding (W : World X G) (P : MapPrices) (w : ℕ → ℝ) (θ : ℝ) : Prop where
  lit k : 0 < w k
  narrow k : w k ≤ P.α k
  shared x i : W.bar.Here x i → i < W.fine x → w ((W.trial x).clock.J i) ≤ bridgeWidth (W.trial x) P i
  gains : 0 < θ
  folds x i : W.bar.Here x i → i < W.fine x →
    2*w ((W.trial x).clock.J i) ≤ ((W.trial x).S.block i).val * w ((W.trial x).clock.J (i+1))
  earned x i : W.bar.Here x i → i < W.fine x →
    quote (W.trial x) P i (w ((W.trial x).clock.J (i+1))) ≤ W.bar.drop θ x i
  top_cap : W.bar.Poly (fun x i=> if i=W.fine x then topTab (W.trial x) P i else 0)

structure Provides (P : MapPrices) : Prop where
  plan x : (H x).Suffices P
  data x i (hi:W.low x ≤ i)(he:i<W.fine x) :
    ((H x).towers (W.fine x) i).T=((destination (W.trial x) (W.fine x) i).duo (W.trial x).clock.kernel.penalty).T

variable {H} {θ : ℝ} {w : ℕ→ℝ}

private theorem existsRows (h : Provides H P) (ht : Funding W P w θ) :
    ∃ (K : X→ℕ→Packet 1 Faces) (cost : Stair.Array X),
       (∀ x i, W.bar.Here x i → FlatRep (H x) (W.fine x) (W.extra x) i (w ((W.trial x).clock.J i)) (cost x i) (K x i)) ∧
       (∀ x i,W.bar.Here x i → 0 ≤ cost x i) ∧
       ∀ x i,W.bar.Here x i → cost x i ≤ W.bar.stepOnly (fun x i=> cost x (i+1)*W.bar.drop θ x i) x i +
          (if i=W.fine x then topTab (W.trial x) P i else 0) := by
  let cost x : ℕ→ℝ := fun i=> topTab (W.trial x) P (W.fine x) * (W.bar.weight θ x i)⁻¹
  have hp x i : 0 ≤ cost x i := by
    have he:= Ω_pos (h.plan x) (W.fine x)
    have hh:= W.bar.weight_pos θ x i; unfold cost topTab; positivity
  have he x : cost x (W.fine x)=topTab (W.trial x) P (W.fine x) := by simp [cost,Rate.Stair.weight,bar]
  have hr x i : cost x i=cost x (i+1)*W.bar.drop θ x i := by
    have hh := W.bar.weight_step θ θ x i
    simp only [sub_self,RG08.Rate.Stair.drop,neg_zero,zero_mul,Real.exp_zero,one_mul] at hh
    unfold cost
    rw [← hh, _root_.mul_inv_rev]
    unfold RG08.Rate.Stair.drop
    field_simp
  have steps x j i (hi : W.bar.Here x i) (hl : j=W.fine x-i):
      ∃ K : Packet 1 Faces, FlatRep (H x) (W.fine x) (W.extra x) i (w ((W.trial x).clock.J i)) (cost x i) K := by
    have hx : i≤ W.fine x := hi.2
    have hy : W.low x ≤ i := hi.1
    induction j generalizing i with
    | zero =>
      have hz : i=W.fine x := by omega
      subst i
      rw [he]
      exact at_end (h.plan x) _ _ (W.earlier x) (ht.lit _) (ht.narrow _)
    | succ j ih =>
      have hL : i < W.fine x := by omega
      obtain ⟨K,hK⟩:= ih (i+1) (Rate.Stair.finer hi hL) (by omega) hL (by omega) -- hy/hx order?
      have hP:= to_here (h.plan x) (W.earlier x) hL (h.data x i hy hL) _ _ _ (ht.lit _) (ht.lit _) (ht.shared x i hi hL) (ht.folds x i hi hL) (hp x (i+1)) K hK
      refine ⟨_,⟨fun y=> (hP.declared y).trans (ENNReal.ofReal_le_ofReal ?_), hP.smooth,hP.covariant,hP.here⟩⟩
      rw [hr x i, mul_comm (cost x (i+1))]; exact mul_le_mul_of_nonneg_right (ht.earned x i hi hL) (hp ..)
  classical
  choose K hk using fun x (i:{i:ℕ // W.bar.Here x i})=>steps x (W.fine x-i.val) i.val i.property rfl -- sigma pack
  refine ⟨fun x i=> if h:W.bar.Here x i then K x ⟨i,h⟩ else 0,cost,fun x i hi=>?_,fun x i _=>hp x i,fun x i hi=>?_⟩
  · dsimp only; rw [dif_pos hi]; exact hk x ⟨i,hi⟩
  by_cases hv : i<W.fine x
  · rw [if_neg (Nat.ne_of_lt hv), Rate.Stair.stepOnly,if_pos (show i<W.bar.top x from hv), ← hr,add_zero]
  have hn : i=W.fine x := le_antisymm hi.2 (Nat.le_of_not_gt hv)
  subst i
  rw [he,if_pos rfl,Rate.Stair.stepOnly,if_neg (show ¬W.fine x<W.bar.top x from hv),zero_add]

/-- Geometric UV rate modulo kernels null on linear curvature; can be inserted in expressions
that factor through indicated Sigils. -/
theorem overlap (h : Provides H P) (ht : Funding W P w θ) :
    ∃ (K : X→ℕ→ Packet 1 Faces) (A : ℝ) (d : ℕ) (c : ℝ), 0≤A ∧ 0<c ∧
       ∀ x i, W.bar.Here x i →
       FlatRep (H x) (W.fine x) (W.extra x) i (w ((W.trial x).clock.J i))
       (A * W.bar.age x i^d * (((W.trial x).S.a (W.fine x)/(W.trial x).S.a i)^c)) (K x i) := by
  obtain ⟨K,cost,H₁,H₂,H₃⟩:=existsRows h ht
  obtain ⟨A,d,c,hA,hC,hB⟩:=
    (Rate.Stair.fade_solve ht.gains H₂ (Rate.Stair.Fade.of_top ht.top_cap (fun x i _ hi=>if_neg (Nat.ne_of_lt hi))) H₃).cap
  refine ⟨K,A,d,c,hA,hC,fun x i hi=>?_⟩
  exact {H₁ x i hi with declared:=fun y=> ((H₁ x i hi).declared y).trans (ENNReal.ofReal_le_ofReal (hB x i hi).2)}

end World
end YM.RG08.Flat
