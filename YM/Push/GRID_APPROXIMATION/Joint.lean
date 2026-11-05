import YM.Push.GRID_APPROXIMATION.Many

/-!
# Signed signal to estimate (on the actual history)

 and  setting. For disconnected *or* connected sectors no
switch of underlying measure. Keep negative terms, pay with the normalized
measure AFTER integrating. The join at k uses ONE push of the marked fine
product, vacant summons still push that same unmarked density. New sources
on the SAME remaining variable. Definitions on full census (all powerset
coefficients), not just observed moments. Scaling with physical a's.

These are exact calculations; see `Estimate` for subsequent use of
BUDGET hypotheses about these finite-cutoff signals; no claim that budgets
are available from the library (unready many-source RG estimates).
-/

set_option autoImplicit false
noncomputable section
namespace YM.Push.GridApprox.Joint
open RG Lattice Wilson MeasureTheory Filter Function Marker Overlay Cells
open scoped Topology BigOperators

variable {G : Gauge} (H : History G) (N p : ℕ) {h k r : ℕ}

abbrev Markers (h p : ℕ) := Stock.census (Site (H.S.side h p))

variable (hk : h ≤ k) (hN : k ≤ N)
variable (O : Config G (H.S.side N p) → ℂ) (F : Config G (H.S.side k p) → ℂ)

/-- Full product of copied *negative* old factors at the fine level. -/
def old (hN : h ≤ N) (s : Finset (Site (H.S.side h p))) (U : Config G (H.S.side N p)) :=
    ∏ i ∈ s, (- (tilesAt H.S p hN).copy i O U)

def fine (hN : h ≤ N) (s : Finset (Site (H.S.side h p))) (U : Config G (H.S.side N p)) :=
    (bare (H.β N p N) U:ℂ) * old H N p O hN s U

def incoming (s : Finset (Site (H.S.side h p))) (V : Config G (H.S.side k p)) :=
    ∏ i ∈ s, (tilesAt H.S p hk).copy i F V

/-- Coefficient after coarse birth (without physical bump). Distinct slots,
commuting square-zero markers. Negative old, positive new. -/
def join (s : Finset (Site (H.S.side h p))) (V : Config G (H.S.side k p)) :=
    ∑ l∈s.powerset, (pushTo H N p hN (fine H N p O (hk.trans hN) (s\l)) V) * incoming H p hk F l V

/-- Accurate signal reaching stop with the level-r bump. Normalization not
optional: coefficients for source encoded as `a_r^d * [source]`. -/
def scaled (hr : r ≤ k) (d : ℕ) (s : (Markers H h p).Mode) (W : Config G (H.S.side r p)) :=
    Ride.bump (H.S.a r) s (fun _ => d) * pushTo H N p hr (join H N p hk hN O F s.val) W

/-- Actual replicated difference on microscopic configurations. Keep the whole
monomial (s=all for root, also allow subsets). -/
def difference := backTo H N p hN F - O

def cutoff (s : Finset (Site (H.S.side h p))) (U : Config G (H.S.side N p)) :=
    ∏ i∈s, (tilesAt H.S p (hk.trans hN)).copy i (difference H N p hN O F) U

section integrals
variable {O F}

lemma fine_env (hO : Envelope O) (hn : h ≤ N) (s) : Envelope (fine H N p O hn s) := by
  have he : Envelope (fun U : Config G (H.S.side N p) => (bare (H.β N p N) U:ℂ)) :=
    Envelope.compactC (Complex.continuous_ofReal.comp (bare_cont _))
  exact he.mulC (Envelope.prodC _ _ fun i _ => (replica_env _ _ hO).negC)

lemma incoming_env (hF : Envelope F) (s : Finset (Site (H.S.side h p))) : Envelope (incoming H p hk F s) :=
    Envelope.prodC _ _ (fun _ _ => replica_env _ _ hF)

lemma portion (hO : Envelope O) (hF : Envelope F) (s l : Finset (Site (H.S.side h p))) :
    Integrable (fun V => pushTo H N p hN (fine H N p O (hk.trans hN) (s\l)) V * incoming H p hk F l V)
      (prior G (H.S.side k p)) := by
  have he := (fine_env H N p hO (hk.trans hN) (s\l)).integrableC (prior ..)
  have hb := incoming_env H p hk hF l; obtain ⟨C,hC⟩ := hb.cost
  exact (pushTo_integrable H N p hN _ he).mul_bdd hb.meas.aestronglyMeasurable (Eventually.of_forall hC)

lemma joined (hO : Envelope O) (hF : Envelope F) (s) :
    Integrable (join H N p hk hN O F s) (prior G (H.S.side k p)) :=
    integrable_finsetSum _ fun l _ => portion H N p hk hN hO hF s l



lemma cutoff_env (hO : Envelope O) (hF : Envelope F) (s : Finset (Site (H.S.side h p))) : Envelope (cutoff H N p hk hN O F s) := by
    have ht : Envelope (difference H N p hN O F) := (backTo_env H N p hN hF).subC hO
    unfold cutoff
    exact Envelope.prodC _ (fun i => (tilesAt H.S p (hk.trans hN)).copy i (difference H N p hN O F)) (fun i _ => replica_env _ i ht)
end integrals

lemma copy_sub {n : Side} (T : Tiling n) (i : T.Cell) (V W : Config G n → ℂ) (U : Config G n) :
    T.copy i (V-W) U = T.copy i V U - T.copy i W U := by
  classical
  unfold Tiling.copy; split <;> simp

/-- Decompose entire joint coefficient, not making any assumption about
factorization of old terms. -/
lemma expand (s : Finset (Site (H.S.side h p))) (U : Config G (H.S.side N p)) :
    cutoff H N p hk hN O F s U =
     ∑ l∈s.powerset, (incoming H p (hk.trans hN) (backTo H N p hN F) l U) * old H N p O (hk.trans hN) (s\l) U := by
  simp_rw [incoming,cutoff,old,difference,copy_sub,sub_eq_add_neg,← Finset.prod_add]

variable {F O}

lemma restored (hO : Envelope O) (w : ℕ) (hF : Interior (window 0 w) F) (hh : room H.levels h k w)
    (s : Finset (Site (H.S.side h p))) :
    (∫ V, join H N p hk hN O F s V ∂prior G (H.S.side k p)) =
      (partition G (H.S.side N p) (H.β N p N):ℂ) * moment (H.β N p N) (cutoff H N p hk hN O F s) := by
  have ht := cylinder_env hF
  let q := hk.trans hN
  let V := Config G (H.S.side k p)
  let U := Config G (H.S.side N p)
  let β := H.β N p N
  let B (s : Finset (Site (H.S.side h p))) := incoming H p hk F s
  let D (s : Finset (Site (H.S.side h p))) := incoming H p q (backTo H N p hN F) s
  have hm (l : Finset (Site (H.S.side h p))) : backTo H N p hN (B l)=D l :=
    backTo_copies H N p hk hN l F w hF hh
  have hx (l) :
      (∫ v : V, pushTo H N p hN (fine H N p O q (s\l)) v * B l v ∂prior G _) =
      ∫ u : U, fine H N p O q (s\l) u * D l u ∂prior G _ := by
    have hj := pushTo_dual H N p hN (F:=B l) (incoming_env H p hk ht l)
      (fine H N p O q (s\l)) ((fine_env H N p hO q (s\l)).integrableC _)
    rw [hm l] at hj; exact hj
  rw [moment_formula β _ ((cutoff_env H N p hk hN hO ht s).integrableC _),mul_inv_cancel_left₀ (Complex.ofReal_ne_zero.mpr (partition_pos _).ne')]
  unfold join; rw [integral_finsetSum _ (fun i _ => portion H N p hk hN hO ht _ i)]
  change (∑ l∈s.powerset, ∫ v : V, pushTo H N p hN (fine H N p O q (s\l)) v * B l v ∂prior G _) = _
  simp_rw [hx]; rw [← integral_finsetSum]
  · apply integral_congr_ae; refine Eventually.of_forall fun u => ?_
    dsimp only; rw [expand,Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_; unfold fine D; ring
  intro l _; exact ((fine_env H N p hO q (s\l)).mulC (incoming_env H p q (backTo_env H N p hN ht) l)).integrableC _

lemma restore_scaled (hO : Envelope O) (w : ℕ) (hF : Interior (window 0 w) F) (hh : room H.levels h k w)
    (hr : r ≤ k) (d : ℕ) (s : (Markers H h p).Mode) :
    (∫ W, scaled H N p hk hN O F hr d s W ∂prior G (H.S.side r p)) =
      Ride.bump (H.S.a r) s (fun _ => d) * ((partition G (H.S.side N p) (H.β N p N):ℂ) *
        moment (H.β N p N) (cutoff H N p hk hN O F s.val)) := by
  unfold scaled; rw [integral_const_mul,pushTo_integral H N p hr _ (joined H N p hk hN hO (cylinder_env hF) s.val),
    restored H N p hk hN hO w hF hh]

variable (F O)
-- Note binder order using {F O} above, check.


end YM.Push.GridApprox.Joint
