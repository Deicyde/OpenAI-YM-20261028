import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Deck.Utopian
/-! # Homogenized optional vertex on Grade fields, even on fine flag equality.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Deck.Stellar
open Function Filter Lattice RG Pressure Tree Wilson Finset Matrix
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open Further.PhysicalPeriodLimitF933 Macrame Bloch Laurent Shell Census Raw Footprint Matter Mint
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval
variable {G : Gauge} {c f C F:Side} {P : Patch} {M D' : ℕ} {K : Teller G}
variable {h : f.val=c.val*P.L.val} {H : F.val=C.val*P.L.val} {Q:KernelChoices} {hC : C.val=c.val*M} {he:2 ≤ c.val}
local notation "L" => Lace.project (h:=h) (H:=H) hC he
local notation "S" => stepped Q h
local notation "Y" => stepped Q H
variable {T: Tube G (stepped Q h)} {T': Tube G (stepped Q H)} {p : ℝ} {E: Forest (stepped Q h).ratio} {E':Forest (stepped Q H).ratio}
    {X: Coat T E} {X': Coat T' E'} (A : Stellar hC he K p X X') {R:RG.Rep G f} {R':RG.Rep G F}
local notation "B" => radiusB p

include A
lemma real_spin (β a : ℝ) (V: ℕ→ Atom G D') (s : BudgetPoint) (i:Raw.Trans F) (hp:atomCharge V i≤ radiusB p) (u : Directions G f) :
    let y:=X.input u; let Y':=X'.input (Deck.light (L).high.cut u); let j:= turn_down (L) i
    Raw.translateValue s V β Y' i= Raw.translateValue s V β y j ∧ X'.enforce a (Deck.light (L).high.cut u) (X'.plaza (atomFoot (decreed H) 0 B V i))=X.enforce a u (X.plaza (atomFoot (decreed h) 0 B V j)):= by
  intro Y₁ Y₂ j
  have he : 4<f.val := by have hs:= A.old.buys; have hm := P.L.property; have hh:c.val≤ f.val:= h ▸ Nat.le_mul_of_pos_right _ hm; omega
  constructor
  · unfold Raw.translateValue Y₂ j; rw [(A.glassU u).2.2,show pull i.1 0 ((L).high.links _)=(L).high.links (pull i.1 0 Y₁) from constellation (fineP h H hC) i.1 _]; apply congr_arg _; exact acts_c (fineP h H hC) _ i.2.1 _ he ..
  let v:= atomFoot (decreed H) 0 B V i; let n:= Mint.width 0 B B
  have hg : 2*(n+3)<c.val:=by unfold n Mint.width; have ht:= A.old.buys; omega
  unfold j; rw [projectionA hC _ _ _ _ _ he]; apply A.porter _ n hg (soul (Y) i)
  exact (batch_span (Y) V 0 B B (lt_of_lt_of_le (by norm_num) A.old.sight.1) i hp).2

variable (hr : R'.path= R.path) (hp : R'.p=R.p) (hf:R'.beta=R.beta) (a:ℝ) (z:Air f G) (O:ChartRatio G)
include hr hp hf
lemma traced (i:Music C F) (hh : verse R'.path i ≤ B): X'.farLog R' a O (blow (L) z) (note i)=X.farLog R a O z (note (verse_down (L) i)):= by
  unfold farLog; rw [hf,A.rolls]; rcases i with i|i|i|i; rotate_left 3
  · exact A.naryL ..
  all_goals
    unfold Mint.note verse_down; dsimp only [Sum.map,Function.comp_apply,Sum.elim]
    unfold Coat.inhale Raw.expo Raw.space; dsimp only [Sum.elim]; rw [hr,hp,A.D.1,A.D.2]; rw [hr] at hh; dsimp only [Mint.verse,Sum.elim] at hh; try rw [hf]
    exact congr_arg₂ _ (A.real_spin _ (2*a) _ R.p i hh (X.liftA R.beta z)|>.1) (A.real_spin (-orientation) (2*a) _ R.p i hh (X.liftA R.beta z)|>.2)
lemma granted (i:Music C F) (hh:verse R'.path i≤ B) (Z :ℝ) (l:ℕ) (k k':Finset ℕ) : X'.vertex R' O Z a k l (blow (L) z) (disc (Y) i)= X.vertex R O Z a k' l z (disc (S) (verse_down (L) i)):= congr_arg (fun v=> Real.exp v-1) (A.traced hr hp hf a z O i hh)
end YM.PhysicalNext.Repeat.Deck.Stellar
