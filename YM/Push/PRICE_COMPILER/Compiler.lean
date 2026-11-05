import YM.Push.PRICE_COMPILER.Post

/-!
# Main price order theorem and paid calendar

Use these before constructing the producer objects. `Permit` records what
this local RRequirements compiler *actually* earns. It is quantitatively
inhabited. Collects exact pre/post-L branches. No existence of e.g.,
Raw Horizon with the purchased rates, a path with the desired stationary
matching & transfer estimates, or a beta curve is claimed.
-/

set_option autoImplicit false
noncomputable section
namespace YM.Push.PriceCompiler
open Filter Function Lattice RG RG.Supply Wilson Precision Pressure Bid
open scoped Topology Matrix.Norms.Frobenius BigOperators

/-- For later reading. Same stamps for EVERY use. -/
structure Permit {G : Gauge} {P : Before} {f : ℕ → ℕ} {D : Rolls (P.sheet G f)}
    (m : Preparations P D) {T : Protection D} {W : Delays T} {Y : Bar W} (I : Wait Y) (a : Levels G) : Prop where
  pre : Before.Funded P G f
  post : m.Ledger W
  paid : Paid I a

variable {G : Gauge}

/-- The two orders in one type.

Take arbitrary Before quotes (from the stipulated part of RRequirements and/or
numerical demands at this cut) with the order stated in Pre. See `order_plans`
to generate order plans given finite needs, `admissions` etc. Then
anticipated L floor `e`, buy FLOOR once and Metals. For ANY larger floor
and ANY Rolls on that sheet (share them!), fix pressure prices with their
w's and β requirements respecting extra lower gates and SceneRate with its
gap. For this interface the two are independent (can also choose gap and w
sequentially). Then PostCost numbers can be fixed, theta shrunk BEFORE W;
`∀ q s` permits their requirements. Entrance, shell etc tests paid at W;
finally actual Wait/Paid. Works under further increases to V as indicated.

`AfterBill` just prices further ERROR EXPENDITURES, not occurrence/proof of a
specific error estimate. No interpretation as an unconditional path/Wilson
result. Nothing here needs an ensemble with the pre/post author, kernel or
Teller properties. -/
theorem compile_prices (hG : G.Simple) (P : Before) (e : ℕ → ℕ) :
    ∃ f, Monotone f ∧ e ≤ f ∧ ∀ g : ℕ → ℕ, f ≤ g →
      Before.Funded P G g ∧ Nonempty (Rolls (P.sheet G g)) ∧ ∀ D : Rolls (P.sheet G g),
      ∀ (w : ℕ → ℕ → ℝ) (η : ℕ → ℝ), (∀ i, 0 < η i) →
      ∃ M : Preparations P D, w ≤ M.w ∧ M.gap ≤ η ∧
        ∀ (q : AfterBill) (s : PostCost D → ℕ → ℝ), (∀ i, 0 < s (M.budget q) i) →
        ∃ T : Protection D, T.theta ≤ s (M.budget q) ∧ ∀ V : Delays T,
          ∃ W : Delays T, OrderedDelays W ∧ DelayLe V W ∧ ∀ U : Delays T, DelayLe W U →
            M.Ledger U ∧ ∀ β : ℝ, ∃ Y : Bar U, β ≤ Y.value ∧ Nonempty (Wait Y) ∧
              ∀ I : Wait Y, ∃ a : Levels G, Permit M I a := by
  obtain ⟨f,hf,he,hF⟩ := P.enoughFloors G e
  refine ⟨f,hf,he,fun g hg => ⟨hF g hg,Rolls.exists_rolls _ hG,fun D w η h => ?_⟩⟩
  obtain ⟨M,hM,hm⟩ := preparations (hF g hg) D w η h
  refine ⟨M,hM,hm,fun q s h => ?_⟩
  obtain ⟨T,hT⟩ := M.withTheta q s h
  refine ⟨T,hT,fun V => ?_⟩
  obtain ⟨W,hw,hV,hW⟩ := M.ledger_exists hG T V
  refine ⟨W,hw,hV,fun U hu => ⟨hW U hu,fun β => ?_⟩⟩
  obtain ⟨Y,hY⟩ := Bar.exists_above U β
  refine ⟨Y,hY,⟨cushion Y 0 0 0⟩,fun I => ?_⟩
  obtain ⟨a,ha⟩ := Wait.ready I hG
  exact ⟨a,hF g hg,hW U hu,ha⟩

/-- Simple nonemptiness corollary for actual ledger use. Real physical costs
still as explicit in consumers, in particular any `q` supplied in the stated
order. -/
theorem permits (hG : G.Simple) (P : Before) (e : ℕ → ℕ) :
    ∃ f, Monotone f ∧ e ≤ f ∧ Nonempty (Rolls (P.sheet G f)) ∧ ∀ D : Rolls (P.sheet G f),
      ∃ (M : Preparations P D) (T : Protection D) (W : Delays T) (Y : Bar W) (I : Wait Y)
        (a : Levels G), Permit M I a := by
  obtain ⟨f,hf,he,h⟩ := compile_prices hG P e
  obtain ⟨-,hm,H⟩ := h f le_rfl
  refine ⟨f,hf,he,hm,fun D => ?_⟩
  obtain ⟨M,-,-,hM⟩ := H D 0 (fun _ => 1) fun _ => zero_lt_one
  let q : AfterBill := ⟨fun _ _ => 1,fun _ _ => 1,fun _ _ => 1,fun _ _ => zero_lt_one,
    fun _ _ => zero_lt_one,fun _ _ => zero_lt_one⟩
  obtain ⟨T,-,hT⟩ := hM q (fun _ _ => 1) fun _ => zero_lt_one
  obtain ⟨W,-,-,hw⟩ := hT ⟨0,0,0,0⟩
  obtain ⟨Y,-,⟨I⟩,hI⟩ := (hw W (DelayLe.refl W)).2 0
  obtain ⟨a,ha⟩ := hI I
  exact ⟨M,T,W,Y,I,a,ha⟩



namespace Permit
variable {P : Before} {f : ℕ → ℕ} {D : Rolls (P.sheet G f)}
    {M : Preparations P D} {T : Protection D} {W : Delays T} {Y : Bar W} {I : Wait Y}
    {a : Levels G} (h : Permit M I a)
include h



lemma larger (m i : ℕ) : Larger (a.clock.op m i) (G:=G) := larger_paid h.post.macroFits h.paid m i

lemma loopCost (m : ℕ) :
    P.slopePrices.cost (a.clock.J (m+1)) (a.clock.J m) (a.S.block m).val (a.clock.loopCap (m+1)) ≤ a.clock.loopCap m :=
  buys_loop P.slopePrices a h.paid m (h.post.loops _ _ (h.paid.pays m) _ (step_paid a m))
    (h.pre.at_edge h.paid m).loopTransfer



lemma factorial (i : ℕ) : (Nat.factorial (a.params i).order:ℝ) ≤ (a.params i).columns := by
  rw [params_eq h.paid]
  exact P.fact_cols G _



/-- Common `r` across all periods, rolls on this clock, histories with
these Levels. -/
lemma authors (e : ℕ → ℕ) :
    ∃ r : ℕ → ℕ, Monotone r ∧ e ≤ r ∧ (∀ d N, r d ≤ N → d ≤ P.orders.degrees.cap (a.clock.J N)) ∧
      ∀ H : History G, H.levels = a →
        Bid.RefLi H (Labels.frames G) (Next.Foundations.localSection G) (Next.Foundations.hol G) r := by
  obtain ⟨r,hr,he,hR⟩ := reference_levels P.orders.degrees a e
  refine ⟨r,hr,he,hR,fun H ha => refs_paid (P.author_cols G) (fun _ => rfl)
    (fun _ => rfl) (P.room_cols G) h.post.orders (?_ : Paid I H.levels) _ ?_⟩
  · rw [ha]; exact h.paid
  rw [ha]; exact hR

/-- Pre-bought K used on delivered ACTUAL raw kernel estimates, retains
beds and A0,T. -/
lemma kernel {B : Horizon a} (hb : P.flat.Estimates a B) :
    ∃ V : Horizon a, Retained V B ∧ V.Suffices (P.frozen G) := by
  have he : ∀ m, (a.params m).clip.direct=(P.clip (a.clock.J m)).direct := fun m => by rw [params_eq h.paid]; rfl
  exact (preMap_props (P.kernelChoice G) P.clip P.flat G).2.2 a he h.paid.kernel B hb.rack
end Permit
end YM.Push.PriceCompiler
