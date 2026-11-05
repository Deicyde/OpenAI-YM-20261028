import YM.TraceExtension.Verse.Part
import YM.TraceExtension.Terrace.Gondola
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Verse
open Function Filter Set Extraction Cells OS OS.Ground Lattice Spec MeasureTheory Wilson
open RG Terrace MergeProof.East Next.Rank Next.Rank.East Next.UVStress Further.CorrectedLift Climb
open Glyph Next.Rank.Station Next.Rank.Tapes.West Analysis Marker Edition
open scoped Topology BigOperators InnerProductSpace Classical ContDiff
variable {G: Gauge} {C: Family G}{𝓛: Ultrafilter (ℕ × ℕ)} {f:Extraction.Order} {S:Table C.book} {V:Chamber S timeAxis}{A:Spread V}{p:A.Resolution}{k b i n d: ℕ}
variable {H:(Cells.standard C).Hierarchy}{J:Scaling S}{W:∀ i,Vane C i}{Y:∀ d _:ℕ,(Cells.standard C).Field d→L[ℂ] C.label d}(hq:Gondola f H J 𝓛 W Y)
local notation "S'"=> Cells.standard C
local notation "A'"=> C.path.levels
local notation "U'"=> (𝓛:Filter (ℕ×ℕ))

def fad (w: Vane C i)(x:Points n):= tested (A') w.b w.k x
def flat (w: Vane C i)(x:Points n):= Next.Rank.Station.choose (A') w.b w.k x
def rum (w: Vane C i)(x:Points n):= Extraction.Order.grid C w.k (flat w x)
lemma raw (w: Vane C i)(x:Points n): rum w x=w.wheel.r • fad w x:=by change _=_ • ((Next.Rank.Station.gap _ _ _)⁻¹ • rum _ _); rw [show w.wheel.r=Next.Rank.Station.gap _ w.b w.k from rfl, smul_smul,mul_inv_cancel₀ (Next.Rank.Station.gap_pos ..).ne',one_smul]

include hq
set_option maxHeartbeats 800000 in
lemma seat (w:Seed C f S)(hf:U' ≤ f.fuse) (R:p.Out)(hv:Steady V){K:p.X→Table C.book}(hs:∀ i,(K i).Hierarchy)(hy:∀ i,p.receives (K i) i)
    (t:Fin 2→PegC C d)(x':p.X)(hr:(K x').respects S): ∀ᶠ i in atTop,∀ x:Points 2, FitSky (A') (W i|>.b) (W i|>.k) x → fad (W i) x ∈ Scaling.window 100 2 →
       let T:= fun j:Fin 2=> PoleC C d (t j)
       let Q:= fad (W i) x
       let m:=Read.maxProfile C Q (fun j=>⟨d,T j⟩)
       ‖S.classMoment (K x') (fun _=>d) (rum (W i) x) (fun j=> J.U i d (T j)) - (S').classMoment (S') (fun _=>d) Q T‖ ≤ costHint i+(‖m.part (Glyph.slot 0)‖+‖m.part (Glyph.slot 1)‖)*costHint i:=by
    filter_upwards [hq.terminal d,eventually_ge_atTop d] with i ⟨hu,hU⟩ hd x h hh T Q m
    let j: Fin (i+1):=⟨d,Nat.lt_succ_of_le hd⟩; let L:= W i; let b:=L.b; let k:=L.k; let y:= flat L x
    have he: rum L x ∈ generic 2:=h.usable
    let v: ℕ→ℕ→Fin 2→C.label d:= fun N p c=> L.wheel.atCut (N,p) j (T c)
    let B: Duo C U' k d:=⟨y,he,fun c i'=> v i'.1 i'.2 c,fun c=> Y d i (T c),fun c=> (Dash.arcing hu (tendsto_const_nhds (x:=T c))).congr fun i'=>by unfold heightV; rw [dif_pos hd]⟩
    let r:=widthSky (A') b k; have hr':r ≤ k:= (widerSky ..).trans (beforeSky ..); let m1(c:Fin 2):= m.part (Glyph.slot c); let UV := Glyph.scene ({0,1}:Finset (Fin 2)); let z:=m.part UV-m1 0*m1 1
    have hC(N p U):
        (Ship.invoiceSky (Next.Rank.Atlas.jointX (d0:=fun _=>d) (fun c=> Further.CorrectedLift.ladder C d (T c))) (q_asked (C:=C) (d:=fun _=>d) (v N p)) h N p U)
        = Read.cylinder (Read.cumulants C Q (fun j=> ⟨d,T j⟩) (Ship.fittingSky h)) (B.shoots N p) U:=by
        have hz: Next.Rank.Atlas.jointX (d0:=fun _=>d) (fun c=> Further.CorrectedLift.ladder C d (T c)) = fun j=> ⟨d,T j⟩:=by funext c; simp only [Atlas.jointX]; rw [ladder_reads]
        rw [hz]; rfl
    have he': B.Buys m1 z r (costHint i):=by
        refine ⟨(cost_pos _).le,hr',?_⟩; filter_upwards [(link_mesh hf).eventually (h.stencils w.cutoff d), (link_mesh hf).eventually_gt_atTop k] with l hp hp'
        obtain ⟨hv,hv'⟩:= hp; let N:=l.1; let e:=l.2; let hvN:k<N:= hp'
        have hx(s:modes (Fin 2))(hu:s.val.Nonempty): (Ship.yardSky C b hvN.le e).rootTest (C.beta N e) (fun U=> (Read.cylinder (Read.cumulants C Q (fun j=> ⟨d,T j⟩) (Ship.fittingSky h)) (B.shoots N e) U).part s) ≤ costHint i:= by
           simp_rw [← hC]; exact (hq.season i).1.plate.boot j t N e hvN x hh h s hu
        refine ⟨hvN.le,fun c=> ⟨hv' _ _ _,?_⟩,?_⟩
        · have hh:= hx (Glyph.slot c) (show ({c}:Finset (Fin 2)).Nonempty from Finset.singleton_nonempty _); simp_rw [Read.cylinder_single (Read.cumulative ..)] at hh; exact hh
        have hh:= hx (Glyph.scene {0,1}) (show ({0,1}:Finset (Fin 2)).Nonempty from Finset.insert_nonempty ..); simp_rw [Read.cylinder_pair (Read.cumulative ..) _ _ _ (show (0:Fin 2) ≠ 1 by decide)] at hh
        exact hh
    have ht:= Duo.receipt B m1 z w hf R hv hs hy x' he'
    have hj : m.part UV=(S').classMoment (S') _ Q T:= by
       have he : UV=Glyph.scene Finset.univ:=by unfold UV; congr 1
       rw [he]; exact Read.profile_full (S') H.laws.toSymmetric Q (Ship.fittingSky h) (fun i=>⟨d,T i⟩)
    have hz: m1 0*m1 1+z=_:= (show m1 0*m1 1+z=(S').classMoment (S') (fun _=>d) Q T by rw[← hj]; unfold z; abel)
    rw [hz] at ht; simp_rw [hU]; rw [S.class_agrees (K x') (hs x').laws.toSymmetric hr _ (generic_conf _ he)]
    exact ht
end YM.Trace.Verse
