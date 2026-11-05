import YM.RemainderComparison.Halo.Gala
import YM.RemainderComparison.Sleet.Deer
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Deck.Roused
import YM.RemainderComparison.Sleet.Spark
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


-- Contract RU arrives with actual per-packet path/mark exponential buffers on all coarse-region render calls.
-- Here support quotes only. Doesn't infer injectivity/nonwinding or label alignment
-- merely from these, RU supplies its presentation used on synchronized local charts.
-- Allow chosen radius/lobe per Q. Stage constants. The two accounts may overlap.
-- Unaffiliated forced charges not under this shrink; E6 strong credits paid separately.

def cloudy (R:Rep G f)(Y:ℕ)(i:ℕ):= ∃ x ∈ (R.activities.reg i).support, ¬(separation (R.activities.reg i).site x ≤ Y)

def shade (R:Rep G f)(Y:ℕ)(i:Wing) := match i with
 | .logKey i=> cloudy R Y i
 | .gasKey _=> False

def ridge (R:Rep G f)(Y:ℕ)(E:Set ℕ) : Set ℕ:= {i | i∉ E ∧ cloudy R Y i}

def pigment (a x:ℝ):=Real.exp (-a*till x)
lemma breadthF (Q:ℝ)(hQ:0<Q) (V:ℝ): Rate G L V (pigment Q):= Rate.cutoff hQ
lemma gustLine (Q:ℝ) (hQ:0<Q) {p:ℝ→ℝ}{z:ℝ} (hp:Rate G L z p)(k:ℕ):
    ∀ᶠ x in atTop, |pigment Q x * p x| ≤ incomingE G L x ∧ ∀ β,inBand (betaF G x L) β → |pigment Q x * p x| ≤ gStep β ^ k := by
    let f x:= (pigment Q x)*p x; have hf (a:ℝ): Rate G L a f:=by simpa using! (breadthF Q hQ (a-z)).mul hp
    filter_upwards [Delay.shift_pos G L,hf (-2) (-(11/10)) (by norm_num), Access.exchange _ k (by linarith only : -(k:ℝ)/2-1 < - (k:ℝ)/2) (hf _)] with x hx hy Hz
    have hp: incomingE G L x= betaF G x L^ (-(11/10):ℝ):= by unfold incomingE; rw [Real.sqrt_eq_rpow,← Real.rpow_neg hx.le, ← Real.rpow_mul hx.le]; norm_num
    exact ⟨hy.trans_eq hp.symm,Hz⟩

variable (E:Set ℕ) (w:ℕ→ℝ)
structure Cost (R:Rep G f)(E:Set ℕ)(Y:ℕ)(x Δ B:ℝ)(w:ℕ→ℝ) : Prop where
   fare i : i∈ ridge R Y E → R.p.supBounds (R.activities.reg i).site (R.activities.reg i).support (R.activities.E i) (w i)
   zero i : i∉ ridge R Y E → w i=0
   roof : Footprint.Anchored (fun i=> (R.activities.reg i).site) (fun i=> (pigment Δ x)⁻¹*w i) (regularExtra R) R.p.supportExponent B
variable {Δ:ℝ}{Y:ℕ}
lemma sails (h:Cost R E Y x Δ B w) : Presents R (ridge R Y E) w (pigment Δ x*B):=by
   refine ⟨h.fare,h.zero,fun i=>?_⟩
   have hp:0 < pigment Δ x:=Real.exp_pos _
   convert! budget_scale hp.le (h.roof i) using 1; ext j; dsimp only; split <;> field_simp; ring

def slump (R:Rep G f)(Y:ℕ)(M:ι→Leaf R)(t:ℝ)(i:ι):= if shade R Y (M i).turn then t else 1
def pigmentY (R:Rep G f)(Y:ℕ)(M:ι→Leaf R)(x Δ:ℝ)(l:ι→ℝ)(i:ι):= slump R Y M ((pigment Δ x)⁻¹) i * l i

def muddy (R:Rep G f)(Y:ℕ) (M:ι→Leaf R) (s:Finset ι):= ∃ i∈ s, shade R Y (M i).turn
variable {U:H.ThinP→Drums M S→ℝ}
lemma color (h:Lyric.Paid M H χ N U)(hΔ:0<Δ)(hl:∀ i,0≤l i)(hp:Ac.Hit (Captain.reachability (H:=H)) Z (fun z=>∑ i:Syllable M H z,
     if Lyric.notes M H z i≤ k then Lyric.Bill M H U z (pigmentY R Y M x Δ l) j i J else 0) a B') : Ac.Hit (Captain.reachability (H:=H)) Z (fun z=>∑ i:Syllable M H z,
     if Lyric.notes M H z i≤ k ∧ muddy R Y M (Lyric.page M H z i) then Lyric.Bill M H U z l j i J else 0) a (pigment Δ x* B') := by
   let t:= pigment Δ x; let f i:=slump R Y M t⁻¹ i
   have he:0<t:=Real.exp_pos _; have hh:t≤1:=by apply Real.exp_le_one_iff.mpr; exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hΔ.le) (Nat.cast_nonneg _)
   have hv:t⁻¹ ≥ 1:= (one_le_inv₀ he).2 hh
   have ht i : 1≤f i:=by unfold f slump; split; exact hv; exact le_rfl
   have hB z w : Lyric.Bill M H U z (pigmentY R Y M x Δ l) j w J= (∏ i,∏ x∈ (w i).val,f x)*Lyric.Bill M H U z l j w J:= by
       unfold Lyric.Bill invests; simp_rw [pigmentY,prod_mul_distrib]; unfold f t; ring
   have hQ z (w:Syllable M H z):0≤Lyric.Bill M H U z l j w J:=mul_nonneg (prod_nonneg fun i _=>prod_nonneg fun i _=>hl i) (Lyric.dividend_nonneg M H χ h z w)
   have hT (z)(w:Syllable M H z)(hp:muddy R Y M (Lyric.page M H z w)) : t⁻¹≤ ∏ i,∏ x∈(w i).val,f x:=by
       obtain ⟨i,hi,hp⟩:=hp
       obtain ⟨a,ha,hb⟩:= mem_biUnion.mp hi
       exact (show t⁻¹≤∏ x∈(w a).val, f x from (show f i=t⁻¹ from if_pos hp) ▸ stepProd f ht hb).trans (stepProd (fun a=>∏ x∈ (w a).val,f x) (fun p=>one_le_prod fun j _=>ht j) ha)
   intro x; have hk:= budget_scale he.le (hp x); refine budget_mono hk (fun z=>?_) (fun z=>?_)
   · dsimp only; split
     · exact mul_nonneg (sum_nonneg fun w _=>by split; exact hQ _ _; exact le_rfl) (Real.exp_pos _).le
     exact le_rfl
   dsimp only; split
   next=>
    rw [← mul_assoc,mul_sum]; apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le; refine Finset.sum_le_sum fun i _=> ?_
    rw [hB]; split_ifs
    next hv hu=>
       rw [← mul_assoc]; exact le_mul_of_one_le_left (hQ _ _) ((show t*t⁻¹=1 from mul_inv_cancel₀ he.ne') ▸ mul_le_mul_of_nonneg_left (hT z i hv.2) he.le)
    next ht hn=> exact False.elim (hn ht.1)
    next h₁ h₂ => exact mul_nonneg he.le (mul_nonneg (prod_nonneg fun a _=>prod_nonneg fun i _=>zero_le_one.trans (ht i)) (hQ _ _))
    next => rw [mul_zero]
   next=> rw [mul_zero]
omit [Fintype ι] in
lemma Scale.clear {P':Type} [Fintype P'] {X' : P'→ Site f}{v:ι→ Finset P'} (h:Scale X' v M (pigmentY R Y M x Δ l) m σ B S)(hΔ:0<Δ): Scale X' v M l m σ B S := by
   let p:=pigmentY R Y M x Δ l
   have he i:1≤ slump R Y M ((pigment Δ x)⁻¹) i:=by unfold slump; split; exact (one_le_inv₀ (show 0<pigment Δ x from Real.exp_pos _)).2 (Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (by linarith) (Nat.cast_nonneg _))); exact le_rfl
   have hh i:0 ≤ l i := nonneg_of_mul_nonneg_right (h.currency _) (zero_lt_one.trans_le (he i))
   have hz i:Palette.wages M l i≤ Palette.wages M p i := mul_le_mul_of_nonneg_right (le_mul_of_one_le_left (hh _) (he i)) (Leaf.profit _)
   exact ⟨hh,fun i hi=> h.pin i (hi.trans_le (hz i)),Extra.Multi.Rooted.mono h.crown (fun i=> mul_nonneg (hh i) (Leaf.profit _)) hz le_rfl le_rfl,h.tolerance,h.sizes⟩
end YM.RemainderComparison.Sleet
