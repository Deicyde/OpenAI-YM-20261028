import YM.RG08.Door.Lark
/-!
# The same-slot recurrence in one history or two. Uniform Y/T assets. Opens *symbol* & curvature audits by
inspection of rigorously assembled strata. -/
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false
noncomputable section
namespace YM.RG08.Door
open Filter Lattice Wilson Exterior Precision Laurent FreeResolvent Profiles Finset Function Next.Free RG Bloch Stationary Conductor Staffer Reflect UVExt.Paths Work.F08 Push.AbsoluteSums
open Quire Shade Loom Vale Needle Tall Planned.PrimaryIntegral295 Place Source Source.Drops Labels
open scoped BigOperators Topology Real
variable {X:Chain} {G:Gauge}{E e r d τ D j t i k m l n s :ℕ}{R θ C w:ℝ}{F:Labels.Frame G d}{Ω:SectionData F}{ν:G.ColorIndex}{D':ChartRatio G}{H:Hol G}{P:KPrices X.kernel}{g:KGate P}{Q:Lending G X.kernel}{S:Prism G X.kernel g Q E}
variable {h:1/2≤R}{hD:d+1≤D} {T:Signals P Q E τ H Ω h hD}
open Wings
variable {I:Type}{u:I→Windows}
local notation "Ⓨ" => menu X
local notation "Δ" => chop X

lemma Tin.lapP {V:Wings u 0→EnvelopeU D R G r} (hp:Tin Ⓨ (Δ θ) V (fun t=>ώ T t.i)) -- fix binder
    (hx:Weighed (Launch.farY (u:=u) X) (fun i=> ((X.S.block i.i).val:ℝ)))(he:θ ≤ 1) : Tin Ⓨ (Δ θ) (fun t:Wings u 1=> V t.up) (fun t=> ώ T (t.i+1)) := by
  obtain ⟨B,hB,H⟩:=hp.serves; let L i:=((X.S.block (i:Wings u 1).i).val:ℝ); have ha: Weighed Ⓨ L:= hx.transfer toLaunch
  refine ⟨_, ((aged_up X hx).sway (sh X) (hB.transfer Wings.up)).times ha,fun i=> Ink.raise (H i.up) ?_⟩
  rw [Pi.mul_apply, mul_assoc]; exact mul_le_mul_of_nonneg_left (continued' X θ he i) (hB.positive i.up)

lemma babyW (t:Wings u 1) : Whole (babyQ G X t) := spray_whole (X.flight t.N t.i) X.kernel.penalty X.kernel.penalty_pos (X.adm t.i)
lemma pollen (t:Wings u 1){U:BoardU D R G}(ht:Marvel k U)(hh:Lank U)(hp: auditT H F U=0)(he:Enabled T u) (b:Letter F)(hs:slot b=r):
   let p:=U e r; let P:= aboard d (babyQ G X t) p; Toute P∧ Polished P ∧ invest H P b=0 := by
  intro p P; let K:= X.flight t.N t.i
  have hv : Abates p (d+1):= held H ht hh hp _ _; have hP: Toute p := seat_made ht
  have hz i := paid_color hP (Carrier.linesOf K X.kernel.penalty) (Carrier.stored K _ X.kernel.penalty_pos (X.adm t.i)) i K.odd h
  have hr : fee b<d+1:= Nat.lt_succ_of_le b.bill
  apply And.intro (tot_weight (tot_sums fun i _=> hz i) _)
  refine ⟨all_aboard K.odd h (babyW (G:=G) t) (hh e r),?_⟩
  change invest H (aboard d (painted G (Carrier.linesOf K X.kernel.penalty)) p) b=0
  rw [payout H h K X.kernel.penalty_pos (X.adm t.i) (by have ht:= (he.stepCap t.toLaunch).trans (X.mono _); omega) (hh e r) hP hv b hr.le hs d,amount_empty H (hh e r) hP hv b hr hs,mul_zero] -- .. binder

variable {δ : Wings u 1→ℝ} {U V:Wings u 1→ReadsU F D R}{b:Letter F}{W:Wings u 1→Session (Letter F)}
-- route τ meter width contains polynomial reserves. Bound ALL Hol tests on this dereference clock
lemma siphon (he:Enabled T u)(hv:∀ i,Boards (U i))(hp:∀ i,auditT H F (U i b)=0)(hU:∀ i,Boards (V i))
    (hV: ∀ j<e,∀ r, Tin (menu X) δ (fun i:Wings u 1=> V i b j r) (fun i=> ώ T i.i))
    (hm : Tin (menu X) δ (fun i=> V i b e r-aboard d (babyQ G X i) (U i b e r)) (fun i=>ώ T i.i)) (j:Letter F)(hk:slot j=r) : Dig Ⓨ δ (fun i=> hot (atlas H (V i)) e j b) := by
  have ht(i: Wings u 1): ώ T i.i≤1:= (le_trans (tick_t T _).1 ((tick_t T _).2)).trans (min_le_right ..)
  have hu : Weighed (menu X) (fun i:Wings u 1=> (ώ T i.i)⁻¹):= he.costs.transfer toLaunch
  let A i:= aboard d (babyQ G X i) (U i b e r)
  let W i:= V i b e r-A i
  simp_rw [atlas_fees, auditT]; rw [hk]; refine Dig.sums _ (sh X) (fun k hk'=> ?_) -- binder signature
  split
  next h₁=>
    have hq:k ≤ r:=mem_range_succ_iff.mp hk'
    by_cases hX:k=r
    · subst k; rw [Nat.add_sub_cancel]; rw [show (fun i=> invest H (V i b e r) j)=(fun i=> invest H (W i) j) from funext fun i=>?_]
      · exact digs H hm (fun i=> T.pos _) ht hu _
      have hW:Toute (V i b e r):= seat_made ((hU i).rank b)
      obtain ⟨hQ,hH,hA⟩:=pollen (e:=e) i ((hv i).rank b) ((hv i).paid b) (hp i) he j hk
      have hW' : Polished (W i) := scarlet (hm.serves.choose_spec.2 i) (T.pos _)
      have HZ: W i+A i=V i b e r:= sub_add_cancel ..
      rw [←HZ, invest_more H j (tot_less hW hQ) hQ hW' hH]; rw [show invest H (A i) j=0 from hA,add_zero] -- uh
    exact digs H (hV (e+k-r) (by omega) k) (fun i=>T.pos _) ht hu j -- actual index is e+k-r
  exact Dig.zero
end YM.RG08.Door
