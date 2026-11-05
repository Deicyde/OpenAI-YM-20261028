import YM.RemainderComparison.Portal.Quota
set_option autoImplicit false
noncomputable section
namespace YM.RemainderComparison.Portal
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
local notation "V'" => Q.costs L μ R.beta x q
local notation "LT" => Mixed.lengths S V' (ConnectedActivityE6.lengths T R)
local notation "Z" => radiusB x





open Marker Next.Rank.Glyph Next.Rank.Exponential Sleet
local notation "Yv" => veil ι
local notation "cardboard" => Stock.census ι
open Boulevard Further.LogJets
local notation "N₀" => Staff M H
local notation "Yp" => Site c
section generic
variable {k':Type}{V:BudgetPoint}{wg:k'→ℝ}{K:k'→Support c}{X:k'→ Config G c→ℝ}
structure Tally {G:Gauge} (V:BudgetPoint)(k':Type)(X:k'→ Config G c→ℝ)(b:ℝ):Prop where
   ruler : Termwise V.order (Boulevard.sunny V) X
   control (U:Config G c) : U∈Boulevard.sunny V → ∀ l:List (Directions G c),l.length ≤ V.order → (∀ i∈l,‖i‖≤V.threshold) → SumBudget (fun i=> ‖leftDerivs (X i) l U‖) b
def unite (X:k'→ Config G c→ℝ)(U:Config G c):=∑' i,X i U
lemma levy (h:Tally V k' X b)(U:Config G c)(hp:U∈Boulevard.sunny V) : Summable (fun i=>X i U)∧ Push.Local.Chart V.order (unite X) U ∧ ∀ l:List (Directions G c),l.length ≤ V.order→(∀ i∈l,‖i‖ ≤ V.threshold) → ‖leftDerivs (unite X) l U‖ ≤ b :=by
   have hs:= h.ruler; obtain ⟨ht,hX⟩:=Termwise.smooth_exchange (Boulevard.sky V) hs U hp
   refine ⟨h.ruler.sums [] (by simp) U hp,ht,fun l hh he=>?_⟩
   have hp:= h.control U hp l hh he; rw [show unite X= (fun U=>∑' i,X i U) from rfl,hX l hh]; exact (norm_tsum_le_tsum_norm hp.2.1).trans hp.2.2

-- at any anchor supplied, even different addresses. Port Boulevard.enclosed to generic support.
lemma fuel (p:k'→Site c)(h:∃ w:k'→ℝ,SumBudget w b∧ ∀ i,V.Regular (K i) (X i) ∧ V.supBounds (p i) (K i) (X i) (w i)) : Tally V k' X b:=by
   obtain ⟨k,hk,h⟩:=h
   have he i (x:Config G c) (hx:x∈Boulevard.sunny V): Healthy V.threshold (K i) x:= by unfold Healthy; rw [Boulevard.smoky hx]; simp
   refine ⟨⟨fun i x hx=> (h i).1.smooth x (he i x hx),fun l hl=>?_⟩,?_⟩
   · let d:= V.threshold+l.toFinset.sum (fun i=> ‖i‖)
     have hd : 0<d:= add_pos_of_pos_of_nonneg V.threshold_pos (sum_nonneg fun i _=> norm_nonneg _)
     have hu : ∀ i∈l, ‖i‖≤d:= fun i hi=> (single_le_sum (fun a _=> norm_nonneg a) (List.mem_toFinset.mpr hi)).trans (le_add_of_nonneg_left V.threshold_pos.le)
     let B:=d/V.threshold; have hb: 0<B:= div_pos hd V.threshold_pos; let Y:=l.map fun i=> B⁻¹ • i
     have hY:Y.length=l.length:= by simp [Y]
     have ht : Y.map (fun i=>B • i)=l:= by simp [Y,List.map_map,Function.comp_def,smul_smul,hb.ne']
     have hh i : ∀ j∈Y,V.dirBound (p i) j:= by
       intro j hj; obtain ⟨a,ha,rfl⟩:=List.mem_map.mp hj; apply Boulevard.tiny
       rw [norm_smul, Real.norm_of_nonneg (inv_pos.mpr hb).le]; apply le_trans (mul_le_mul_of_nonneg_left (hu _ ha) (inv_nonneg.mpr hb.le)); apply le_of_eq; unfold B; field_simp
     refine ⟨fun i=> B^Y.length * k i,hk.2.1.mul_left _, fun i x hx=>?_⟩; rw [← ht, March.expands,norm_smul,Real.norm_of_nonneg (pow_pos hb _).le]; exact mul_le_mul_of_nonneg_left ((h _).2.2 x (he i x hx) Y (hY ▸ hl) (hh i)) (pow_nonneg hb.le _)
   intro U hU l hl hV; exact budget_mono hk (fun _=> norm_nonneg _) (fun i=> (h _).2.2 U (he i U hU) l hl (fun i hi=> Boulevard.tiny (hV i hi) _))
end generic
variable (V:BudgetPoint) (E:Set (Staff M H))
-- no additional mask. use on AUX torus only, at all-strict points

def heed (z:N₀)(U:Config G c):ℝ:= if z∈E then Sleet.charge M H χ l z U else 0
def ringSet (p:modes ι): Set N₀ := {z| Turns M H z.1 z.2 ∧ p=scene (page M H z.1 z.2)}
def bar (E:Set (Staff M H)) := unite (heed M H χ l E)
omit [Fintype ι] in
lemma heat (h:Rendition M H χ l V E a b)(ha:0≤ a) : Tally V N₀ (heed M H χ l E) (Fintype.card (Site c)*b) := by
   obtain ⟨w,hv,-,hz,hw⟩:= h.receipt
   let p z:=(Beam.dashboard H (z:N₀).1).site
   have hr z:p z∈Base M H z:= by rw [← show (Beam.dashboard H z.1).support=Base M H z from Beam.see ..]; exact (Beam.dashboard H z.1).anchor
   apply fuel (K:=Base M H) p
   refine ⟨w,?_,fun z=>?_⟩
   · have h:= Labels.anchor_weaker _ _ hv hw p hr; convert budget_mono (budget_over univ _ _ fun x hx=> h x) hv ?_ using 1
     · rw [sum_const,nsmul_eq_mul,card_univ]
     intro x; simp only [sum_ite_eq,mem_univ,↓reduceIte]; exact le_mul_of_one_le_right (hv _) (Real.one_le_exp (mul_nonneg ha (Nat.cast_nonneg _)))
   by_cases he:z∈ E
   · rw [show heed M H χ l E z= _ from funext (fun V=> if_pos he)]; exact ⟨(hz z he).1,(hz z he).2 _ (hr z)⟩
   rw [show heed M H χ l E z=(fun _=>0) from funext fun x=> if_neg he]
   have hp:= AnalyticBridge.CouplingShape.sup_const (G:=G) (p:=V) (o:=p z) (X:=Base M H z) (0:ℝ); rw [abs_zero] at hp
   exact ⟨AnalyticBridge.CouplingShape.reg_const _, hv _, fun _ h l hp' hh=> (hp.2 _ h l hp' hh).trans (hv z)⟩

lemma thins (z:N₀)(p:modes ι)(h:z∈ ringSet M H p) : Lyric.notes M H z.1 z.2=p.val.card:=by
   obtain ⟨hr,hp⟩:=h; rw [hp]; exact (Finset.card_biUnion hr).symm

variable (hx:V.threshold=Pressure.temp x) {p:modes ι}
include hx
lemma potion (h:Tally V N₀ (heed M H χ l (ringSet M H p)) b)(U:Config G c)(hr:U∈Boulevard.sunny V) : shelf M H χ l U p = bar M H χ l (ringSet M H p) U:=by
   have hx':flags (Pressure.temp x) U=∅:=hx ▸ smoky hr
   have h':=(levy h U hr).1
   unfold shelf bar unite; rw [h'.tsum_sigma]
   apply tsum_congr; intro i; rw [tsum_fintype]; apply sum_congr rfl; intro j hj
   have he : Lyric.cut M H χ i j U= string M H χ i j U:= masked_eq _ _ _ _ (by unfold Healthy; rw [hx']; simp)
   unfold heed; split; next h'=> rw [if_pos (show Sigma.mk (β:=Syllable M H) i j∈ringSet M H p from h'), he]; rfl
   next h'=> rw [if_neg (show Sigma.mk (β:=Syllable M H) i j∉ringSet M H p from h')]
lemma lock (hh:E ⊆ ringSet M H p) {v:ℝ} (h:Tally V N₀ (heed M H χ l (ringSet M H p \ E)) b)(ht:Tally V N₀ (heed M H χ l E) v)(U:Config G c)(hp:U∈Boulevard.sunny V):
    shelf M H χ l U p = bar M H χ l E U + bar M H χ l (ringSet M H p \ E) U:=by
   have hx':flags (Pressure.temp x) U=∅:=hx ▸ smoky hp
   have h := (levy h U hp).1; have ht:= (levy ht U hp).1
   let g z:= heed M H χ l E z U+heed M H χ l (ringSet M H p \ E) z U
   unfold shelf bar unite; rw [← Summable.tsum_add ht h,Summable.tsum_sigma (f:=fun i=>_) (show Summable g from ht.add h)]
   apply tsum_congr; intro i; rw [tsum_fintype]; apply sum_congr rfl; intro j hj
   have he : Lyric.cut M H χ i j U=string M H χ i j U:= masked_eq _ _ _ _ (by unfold Healthy; rw [hx']; simp)
   unfold heed; by_cases hx: (Sigma.mk (β:=Syllable M H) i j)∈E
   · rw [if_pos (show Turns M H i j∧ _ from hh hx),if_pos hx,if_neg fun h=>h.2 hx,he,add_zero]; rfl
   rw [if_neg hx,zero_add]; split
   next h'=> rw [if_pos (show Sigma.mk (β:=Syllable M H) i j ∈ (ringSet M H p \ E) from And.intro (show Sigma.mk (β:=Syllable M H) i j∈ringSet M H p from h') hx),he]; rfl
   next h'=> rw [if_neg fun h=> h' h.1]
end YM.RemainderComparison.Portal
