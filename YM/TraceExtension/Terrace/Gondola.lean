import YM.TraceExtension.Terrace.Turn
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Terrace
open Function Filter Set Lattice RG Wilson Labels Source MergeProof MergeProof.Accent Extra.Histories Bid Zn
open Extraction Next.UVStress Next.Rank.Price Next.Rank.East MergeProof.East Further.CorrectedLift Ward Climb
open scoped BigOperators Topology Matrix.Norms.Frobenius ContDiff Classical
variable {G:Gauge}{C:Family G} {F: Extraction.Order} {𝓛: Ultrafilter (ℕ×ℕ)}
set_option quotPrecheck false
local notation "a!"=> (𝓛:Filter (ℕ×ℕ))
local notation "A"=> C.path.levels
local notation "B"=> Climb.Bel C.book
variable {Z:Arch C} (hZ:steep 𝓛 Z){d k i j:ℕ} {S:Table C.book}{X: Scaling S} {a : (Cells.standard C).Hierarchy}
local notation "T!"=> C.labels.level d
section
/-- aligned common choices, including any nonunit representative. -/
def heightV (V:∀ i,Vane C i)(i d:ℕ) (z:ℕ×ℕ): (Cells.standard C).Field d →L[ℂ] C.label d:= if h:d ≤ i then (V i).wheel.atCut z (⟨d,Nat.lt_succ_of_le h⟩: Fin (i+1)) else 0
structure Gondola (F : Extraction.Order) (a:(Cells.standard C).Hierarchy) (X: Scaling S)(𝓛: Ultrafilter (ℕ×ℕ))(V:∀ i,Vane C i) (Y:∀ (d i:ℕ), (Cells.standard C).Field d→L[ℂ] C.label d) :Prop where
    growth : Tendsto (fun i=> (V i).k) atTop atTop
    season : ∀ i,(V i).checked F a i ∧ (V i).wheel.r=X.r i
    terminal : ∀ d:ℕ, ∀ᶠ i:ℕ in atTop,Tendsto (heightV V i d) (𝓛:Filter (ℕ×ℕ)) (𝓝 (Y d i)) ∧ ∀ z,X.U i d z=S.project d (Y d i z)
lemma gravity (h:S.Hierarchy)(ht: StarPath F a X h 𝓛) :∃ V Y,Gondola F a X 𝓛 V Y:=by
    obtain ⟨V,hv,hP,hL⟩:= ht.money
    let X' := C; have hz(d):∀ᶠ i in atTop,∃ Y:(Cells.standard C).Field d→L[ℂ] C.label d,Tendsto (heightV V i d) a! (𝓝 Y)∧∀ z,X.U i d z=S.project d (Y z):=by
       filter_upwards[hL d,eventually_ge_atTop d] with i hi hp; let j:Fin (i+1):=⟨d,Nat.lt_succ_of_le hp⟩; obtain ⟨U,hU,hΩ⟩:= hi j rfl
       refine ⟨U j,?_,hΩ⟩; exact (tendsto_pi_nhds.mp hU j).congr (fun v=>by unfold heightV; rw [dif_pos hp])
    let Y d i: (Cells.standard C).Field d→L[ℂ] C.label d:= if h:∃ Y:(Cells.standard C).Field d→L[ℂ] C.label d,Tendsto (heightV V i d) a! (𝓝 Y)∧∀ z,X.U i d z=S.project d (Y z) then Classical.choose h else 0
    refine ⟨V,Y,hv,hP,fun d=>?_⟩; filter_upwards [hz d] with i hi; unfold Y; rw[dif_pos hi];exact Classical.choose_spec hi
end
variable (H:C.Makes) (hb: (𝓛:Filter (ℕ×ℕ)) ≤ F.fuse)
variable {V:∀ i,Vane C i}{Y:∀ (d i:ℕ),(Cells.standard C).Field d→L[ℂ] C.label d}(hq:Gondola F a X 𝓛 V Y)
def Stern (V:∀ i,Vane C i) (i:ℕ):= summit (A) (V i|>.k)
include hq hZ H hb
lemma sky_tip (d:ℕ)(ht:d≤5)(hG:G.Simple):∀ᶠ i in atTop,let k:=V i|>.k; let F':=C.labels.level d; let q:=Z.β k*X.r i^d
    ∀ v:(Cells.standard C).Field d,Cgrade F' (Further.CorrectedLift.ladder C d v) →
         F'.coeffSize (swale Z d k (Y d i v)-q • F'.core (Further.CorrectedLift.ladder C d v)) ≤ AgeK (A) (-(1/2:ℝ)) k*(2*q*F'.coeffSize (F'.core (Further.CorrectedLift.ladder C d v))):=by
    filter_upwards [hq.terminal d,eventually_ge_atTop d] with i hI he k Z' q v hv
    let u:=Further.CorrectedLift.ladder C d v; let W j:= heightV V i d j v; let y(j:ℕ×ℕ):= C.path.β j.1 j.2 k*(X.r i)^d; let m:=Next.Rank.Station.mag (A) (V i).b k; have hm:0 < m:= Next.Rank.Station.mag_pos ..; let j': Fin (i+1):=⟨d,Nat.lt_succ_of_le he⟩
    obtain ⟨hh,hκ⟩:= hq.season i
    have hp:Tendsto y a! (𝓝 q):=(hZ.mintS k).mul_const _
    let F' := Z'.core u
    have hz:= hp.smul (tendsto_const_nhds (x:=F'))
    have hr : X.r i=C.S.a k*m:=hκ.symm
    have hs:= topPitch hZ (hh.early j') (Dash.arcing hI.1 (tendsto_const_nhds (x:=v)))
    let G':= (( hp.const_mul 2).mul_const (Z'.coeffSize F')).const_mul (AgeK (A) (-(1/2:ℝ)) k)
    refine le_of_tendsto_of_tendsto ((continu Z').continuousAt.tendsto.comp (hs.sub hz)) G' ?_
    filter_upwards [(link_mesh hb).eventually_gt_atTop k] with j hj
    let T := (V i).R j.1 j.2 j'; have hh':InvoiceSky C k j.1 j.2 d T:=(hh.rate _ _ hj).2 j'; change Z'.coeffSize (spine C d k j.1 j.2 (heightV V i d j v)-y j • F') ≤ _*(2*y j * _)
    unfold heightV y; rw [dif_pos he,hr];
    exact via_step H T (((hh.rate _ _ hj).1 j').1) hh' (hh.early j') hj.le _ _ hm.le ht hG hv
omit H hZ
lemma cruise (d:ℕ) :∀ᶠ i:ℕ in atTop,∀ v:(Cells.standard C).Field d, Y d i ((Cells.standard C).conj a.spin d v)=star (Y d i v) ∧ ∀ s:Signed, Y d i ((Cells.standard C).mirror a.spin d s v)= (C.labels.level d).act s.ortho (Y d i v):=by
   filter_upwards [hq.terminal d,eventually_ge_atTop d] with i he hv v
   let j: Fin (i+1):=⟨d,Nat.lt_succ_of_le hv⟩; let V':=V i; let Y':=Y d i
   have ht(v):Tendsto (fun x=> heightV V i d x v) a! (𝓝 (Y' v)):=Dash.arcing he.1 tendsto_const_nhds
   have hx(x)(u: (Cells.standard C).Field d): heightV V i d x u=V'.wheel.atCut x j u:=by unfold heightV; rw[dif_pos hv]
   constructor
   · apply tendsto_nhds_unique_of_eventuallyEq (ht _) (ht v).star
     filter_upwards [(show ∀ᶠ x:ℕ×ℕ in F.fuse, ∀ j x', V'.wheel.atCut x j ((Cells.standard C).conj a.spin j x')=star (V'.wheel.atCut x j x') from (hq.season i).1.fares.lift_real).filter_mono hb] with x hh
     change heightV _ i d x _=star (heightV _ i d x _); rw[hx,hx]; exact hh j v
   intro s; apply tendsto_nhds_unique_of_eventuallyEq (ht _) (((C.labels.level d).act s.ortho).continuous_of_finiteDimensional.continuousAt.tendsto.comp (ht v))
   filter_upwards [(show ∀ᶠ x:ℕ×ℕ in F.fuse,∀ j s v,(V').wheel.atCut x j ((Cells.standard C).mirror a.spin j s v)=C.book.mirrorGroup j s (V'.wheel.atCut x j v) from (hq.season i).1.fares.lift_signed).filter_mono hb] with x hh
   change heightV V _ _ x _= (C.labels.level d).act s.ortho (heightV V i d x v); rw[hx,hx];exact hh j s v
end YM.Trace.Terrace
