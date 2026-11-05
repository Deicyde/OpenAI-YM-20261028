import YM.TraceExtension.Terrace.Meteor
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Terrace
open Function Filter Finset Set Lattice RG Wilson Labels Source MergeProof MergeProof.Accent Extra.Histories Bid Zn
open Extraction Next.Rank.Price Next.Rank.East MergeProof.East Further.CorrectedLift Ward Climb Analysis StressFlux Next.UVStress
open Further.PhysicalPeriodLimitF933 Next.Rank.Spindle Cells PhysicalNext.Repeat.Legato.Bandage Push.GridApprox Next.Rank.Station
open UVNext.FreeStress (camera)
open MeasureTheory
open scoped BigOperators Topology Matrix.Norms.Frobenius ContDiff Classical
variable {G:Gauge}{C:Family G}
set_option quotPrecheck false
local notation "A"=>C.path.levels
local notation "V!"=> C.labels.level 5
variable (P:C.Makes) (h:G.Simple)(θ:PostT C.path.levels)(K:Stock.Tabs C.path.levels) {W:Bid.Worth}{u ψ φ δ:ℕ→ℝ}{r:ℕ→ℕ}{D:∀ N p m:ℕ,m<N→GaugeDoor (C.path.rep N p (m+1)) (C.path.rep N p m)}
variable (ht:Scrim C W u ψ φ δ (fly C.path.levels) r D)(hM:Sceptre C W)
variable {F:Extraction.Order}{𝓛:Ultrafilter (ℕ×ℕ)} {S:Table C.book} {Z:Arch C} {X:Scaling S}
variable (hb:(𝓛:Filter (ℕ×ℕ)) ≤ F.fuse) (hS:S.Hierarchy) (HF:F.PointLimits C S)
variable {V:∀ i,Vane C i}{Y:∀ d i:ℕ,(Cells.standard C).Field d→L[ℂ] C.label d}{H:(Cells.standard C).Hierarchy}
variable (hq:Gondola F H X 𝓛 V Y) (hp:StarPath F H X hS 𝓛)
local notation "b!"=> (𝓛:Filter (ℕ×ℕ))
local notation "m!"=>Stern V
lemma told (k:ℕ)(N p:ℕ)(l:Fin 2→ Cover)(x:C.label 5)(w:C.label 4)(hi:k ≤ N) :
    C.numeric N p ![⟨5,x⟩,⟨4,w⟩] (location C.S k N p ∘ l)=pew C.S hi (C.beta N p) (wrap _ (l 0)) (wrap _ (l 1)) (C.O N p x 0) (C.O N p w 0):=by
    rw [C.num]; simp_rw [Fin.prod_univ_two]; apply congr_arg (Wilson.moment (C.beta N p)); funext U
    let z(i:Fin 2):=anchor C.S p hi (wrap _ (l i)); simp only[Function.comp_apply,Cells.location,dif_pos hi]; change C.O N p x (z 0) U*C.O N p w (z 1) U=C.O N p x 0 (Lattice.translate (z 0) U)*C.O N p w 0 (Lattice.translate (z 1) U); rw [C.translation,C.translation,zero_add,zero_add]

-- Native Y coverage and scaling is applied afterwards. Thus this mission priced independent of the lift at horizon phase.
structure Mission (V:∀ i,Vane C i)(𝓛: Ultrafilter (ℕ×ℕ))(t:ℕ → ℕ×ℕ→C.label 5)(x:ℕ → C.label 5):Prop where
    terms : ∀ᶠ i:ℕ in atTop,Tendsto (t i) (𝓛:Filter _) (𝓝 (x i))
    finances : ∃ m:ℕ, ∀ᶠ i in atTop, let j:=V i|>.k; let k:=Stern V i; ∀ᶠ p: ℕ×ℕ in (𝓛:Filter _), ∃ h:k< p.1, Probe C m j p.2 p.1 h ((C.S.a j ^ (5:ℕ)) • t i p)
variable (t:ℕ → ℕ×ℕ→ C.label 5)(x:ℕ→ C.label 5)(hy:Mission V 𝓛 t x)
include ht hM P hb h θ K hS HF hq hy
lemma ear_price (w:(Cells.standard C).Field 4): ∀ᶠ i in atTop, let j:=V i|>.k; let y:= X.r i • beaconV i V
      ‖S.useAt S y ![⟨5,(C.S.a j)^ (5:ℕ) • S.project 5 (x i)⟩,⟨4,X.U i 4 w⟩]‖ ≤ Tau (A) j (-100):=by
    obtain ⟨m,hm⟩:=hy.finances
    let U:= Further.CorrectedLift.ladder C 4 w
    filter_upwards [hm,hy.terms,hq.terminal 4,hq.growth.eventually (mileage h θ K P ht hM m U),eventually_ge_atTop (4:ℕ)] with i hi hπ hz hk hθ
    intro j y; let l:= (![nearPoint (b_zoom V i),0]:Fin 2→ Cover); let a:= C.S.a j; let b i₁:=t i i₁; let R:(ℕ×ℕ)→C.label 5:= fun u=>a^ (5:ℕ) • b u; let p j:= heightV V i 4 j w
    have hF:Tendsto p b! (𝓝 (Y 4 i w)):= Dash.arcing hz.1 tendsto_const_nhds
    let Y':=y; let T:=y; have he:y= Extraction.tag a l:=kamago hq _; have hκ:0<b_zoom V i:= shine _; have hx:y∈generic _:=(he.symm ▸ clearNear hκ (C.S.a_pos j));
    have hP := proxi hb HF hS 4 j l (he ▸ hx) R p _ _ (hπ.const_smul (a^ (5:ℕ))) hF
    rw [← he, ← hz.2,show S.project 5 _= _ from ((S.project 5).restrictScalars ℝ).map_smul (a^ (5:ℕ)) (x i)] at hP
    apply le_of_tendsto hP.norm; have hL : Injective l:=by intro i j he'; apply generic_conf _ hx; rw [he]; unfold Extraction.tag; simp only[points_apply]; rw[he']
    have hb':1 ≤ b_zoom V i:= Real.one_le_rpow (Real.one_le_exp (sq_nonneg _)) (le_trans (by norm_num : (0:ℝ)≤5) (hq.season i).1.high.1.le)
    filter_upwards [hi,(link_period hb).eventually hk,(link_period hb).eventually (sparse C.S j l hL), (range 6).eventually_all.mpr (fun d _=>(link_mesh hb).eventually (Stock.clear_interior C P j d))] with o ⟨hw,hW⟩ hra hσ hB
    let N:=o.1; let s:=o.2;
    let m':=(V i).R N s (⟨4,Nat.lt_succ_of_le hθ⟩:Fin (i+1)); have hN:j<N:= lt_trans (stellar ..) hw; have hm':Tested C 4 j N s m':=(((hq.season i).1.rate N s hN).1 (⟨4,Nat.lt_succ_of_le hθ⟩:Fin (i+1))).1;
    have hu:p o=ladd C (b_zoom V i) j N s 4 m' U:=by unfold p heightV; rw [dif_pos hθ]; rfl
    rw [told j N s l _ _ hN.le,hu]; refine hra _ hw _ hm' (b_zoom V i) hb' (tiltP _ (hq.season i|>.1.high.2)) (fun d he v=>?_) _ hW _ _ (hσ.ne (show (0:Fin 2)≠1 by decide))
    obtain ⟨hv,H⟩:= hB d (mem_range.mpr (by omega)); exact H s 0 v
end YM.Trace.Terrace
