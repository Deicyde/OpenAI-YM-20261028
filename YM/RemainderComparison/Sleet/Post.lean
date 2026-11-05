import YM.RemainderComparison.Sleet.Glow
import YM.RemainderComparison.Halo.Strike
/-!
 # Stop before analytic letters with storms or sigma ledger
 Per L x, weighted price on SAME H,M. Doesn't assume integrability near
 a dominant sector nor replacing rare flags by analytic profile here.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RemainderComparison.Sleet
open Function Filter Lattice RG RG.Patch Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Mask Work.F03 Presented LabelSum Sector Footprint Packets SliceRows Control Window Pulse PhysicalNext.Repeat Gas
open Coat Matter ProbabilityTheory Poll Pond Census Blaze Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Shield Eider Flux Art Silica Poll Pond Lotus
open Itinerary Animals March Captain Stained Ursell Trees Reserves
open Merge Palette Next.Scheduling Raw Itinerary Opacity Cascade Lyric Daisy Halo Height
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {ι : Type} [Fintype ι]
variable {G : Gauge} {c f L : Side} {S : StepData c f} {P:Teller G} {T: Tube G S} {F : Tree.Forest S.ratio} {R : Rep G f}
    {p : Molecule S} {m : ℕ} {W a r σ μ x κ C : ℝ}
    {Q: YM.ConnectedActivityE6.Target G P} {o: ConnectedActivityE6.Target.Order G W}
variable (M:ι→Lotus.Leaf R)(H:Cash W x μ L Q o C T R) {q A B b e u v d L' Gp:ℝ}{j n k s J:ℕ}(χ:Chi)
variable (N: Captain H j q d v u A b r B e n χ) (Ξ:Utopia H j v d r q χ)
variable (l:ι→ℝ) {T' S' δ B' b' τ ε:ℝ}
local notation "D" => grow G L x
local notation "V'" => Q.costs L μ R.beta x q
local notation "LT" => Mixed.lengths S V' (ConnectedActivityE6.lengths T R)
local notation "Z" => radiusB x
lemma narrow (hv:Massive k Ξ)(hh:1≤D) : Heavy Ξ:=by
    have he : Sales Z Q.relative Q.ε (footprints T R Q.halo Z) (fun i=> D^glow k i*Ξ.flair i) (Sum.elim (Raw.forcedExtra R) (Sum.elim (exCharge T R) fun _=>0)) (Q.goal L x):=hv
    unfold Heavy; rw [← one_mul (Q.goal L x)]
    apply Sales.shift he zero_le_one _ _
    · exact fun i=>mul_nonneg (pow_nonneg (zero_le_one.trans hh) _) (Ξ.uses.nonneg i)
    intro i; rw [one_mul]; refine mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hh ?_) (Ξ.uses.nonneg i)
    rcases i with i| (i | i)
    · exact le_rfl
    · rcases i with i|i|i <;> simp [horn, glow, Clutch.teeth,Clutch.truce]
    simp [horn,glow]

-- Weighted ready with minor marker ambitions (Marker.Root stays separately); exploit Premium

def inkF (S:StepData c f) (k:ℕ) (g:ℝ) (z:Head S):= g^(Sum.elim (fun _=>0) (glow k) z)
local notation "f'" => inkF S k D
lemma stamps (hD:1≤ D)(hp:Massive k Ξ) : Ac.Hit H.supportP Z (tariff (fun i=> f' i * Ξ.fare i) LT 0 Q.ε) Q.relative (V').rootHit :=by
   let z p:= D^glow k p * Ξ.flair p; let g (i:Head S):= f' i * Ξ.fare i
   have hh : Ready H.supportP Z (tariff g LT (Mixed.stamp S V') Q.ε) (Q.exp+2*Q.ε) (V').rootHit Q.δ (1/2):=by
      rw [show g=Mixed.costs S Q.halo Z (steamP S V') z from ?_]; swap
      · funext p; rcases p with p|p
        · unfold g inkF Utopia.fare stout Mixed.costs
          simp
        rfl
      exact Mixed.ready_vertices S Q.halo Z V' H.birth z (ConnectedActivityE6.lengths T R) (steamP S V') Ξ.lives ⟨Ξ.accrues.packetBound,(show Sales _ _ _ _ _ _ _ from hp).nonneg,Ξ.accrues.extra,(show Sales _ _ _ _ _ _ _ from hp).hit⟩
   have h i:0 ≤ g i:=mul_nonneg (pow_nonneg (zero_le_one.trans hD) _) (Ξ.fares i)
   apply Labels.raise_prices _ _ (fun i=>mul_nonneg (h i) (Real.exp_pos _).le) hh.2.2.2.2.2
   intro i; apply mul_le_mul_of_nonneg_left _ (h i)
   exact Real.exp_monotone (add_le_add_right (mul_nonneg Ξ.lives.marked (Nat.cast_nonneg _)) _)

variable {P':Type} [Fintype P'] {s':P'→ Site f} {t:ι→ Finset P'}
local notation "X'" => Palette.mark M (c:=c)
local notation "λ₀" => Lyric.mulScale ((tax G L x)⁻¹) l
local notation "XX" => Lyric.ink Q L x m Gp
lemma opening (K:ℕ) (hp: Massive K N.conduit)(hv:Scale s' t M l m σ Gp S)(hr:radiusCost Q L σ)
      (h:Premium Q L x a μ b' B j n k s J m Gp)
      : Ready H.smallAt Z (fun z=> Lyric.roof M H (floats M H χ N) λ₀ (merit M H (inkF S K D)) z j) (a+b') (salaries Q L μ x B (XX) j n) b' (1/2):=by
   let f:= inkF S K D; let q':= (V').rootHit; let F':=Lyric.combined M (fun i=> f i*N.conduit.fare i) λ₀
   have hL:= H.laws.data.funds.length_eq; obtain ⟨hh,-, hV⟩:= Lyric.habitats M H l hv h.roll (by rw [H.laws.intake.sizes,hL]; exact h.visit.covers) hr
   have hX : Ac.Hit H.birth Z (tariff (Tickets.extra X' (Palette.wages M λ₀)) (ConnectedActivityE6.lengths T R) 0 Q.ε) Q.relative XX:=hV
   have he₁:0 ≤ XX:=budget_nonneg (hX 0)
   have ha:0 < q':= (Mixed.ready_vertices _ _ _ _ _ _ _ _ N.conduit.lives N.conduit.accrues).1
   let k':= D*(q'+XX); have he':0 ≤ q'+XX:= add_nonneg ha.le he₁
   have hF' i : 0 ≤ F' i:= prize M λ₀ _ _ hh N.conduit.fares (fun i=> pow_nonneg (zero_le_one.trans h.roll) _) i
   have hp' : Ready H.supportP Z (tariff F' LT 0 Q.ε) (Q.exp+2*Q.ε) k' Q.δ (1/2):=by
      refine ⟨mul_pos (zero_lt_one.trans_le h.roll) (add_pos_of_pos_of_nonneg ha he₁),Q.pos,h.pace,by norm_num,fun i=>mul_nonneg (hF' i) (Real.exp_pos _).le,fun i=>?_⟩
      have ht := budget_plus (stamps H χ N.conduit h.roll hp i) (pricingL (q:=q) M H XX λ₀ hX i)
      apply budget_loosen _ (le_mul_of_one_le_left he' h.roll); convert! ht using 1
      ext z; unfold F' Lyric.combined tariff; dsimp only; split_ifs ; unfold Target.relative; ring
      simp
   exact Halo.boats M H N.conduit.fare f n B λ₀ N.balance hF' h.visit.allow h.visit.win hp' h.stamp

end YM.RemainderComparison.Sleet
