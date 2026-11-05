import YM.TraceExtension.Slate.April
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Slate
open Function Filter Lattice RG Wilson Labels Source Extra.Histories Bid MergeProof.Accent MergeProof
open Extraction Next.Rank.Price Next.Rank.East MergeProof.East Further.CorrectedLift Climb Analysis Work
open MeasureTheory
open Further.PhysicalPeriodLimitF933 Shunt Weir PhysicalNext.Repeat.Legato.Bandage Push.GridApprox Cells
open Relay Pull Terrace Terrace.Glade Perfect Turret Margin
open scoped BigOperators Topology Matrix.Norms.Frobenius ContDiff Classical
variable {G:Gauge}{C:Family G}
variable (P:C.Makes) (h:G.Simple) (θ:PostT C.path.levels)(K:Stock.Tabs C.path.levels)
variable {W:Worth}{u ψ φ δ:ℕ→ℝ}{r:ℕ→ℕ}{D:∀ N p i:ℕ,i<N→GaugeDoor (C.path.rep N p (i+1)) (C.path.rep N p i)}
variable (ht:Scrim C W u ψ φ δ (fly C.path.levels) r D)(hM:Sceptre C W) (hT:supportQ C.path.levels)
variable {F:Extraction.Order}{𝓛:Ultrafilter (ℕ×ℕ)} (hb:(𝓛:Filter (ℕ×ℕ))≤F.fuse)
set_option quotPrecheck false
local notation "A"=> C.path.levels
local notation "V!"=> C.path
local notation "b!"=> (𝓛:Filter (ℕ×ℕ))
local notation "H!"=> C.path.levels.clock.hatBeta
variable {t:Tickets C} (hu:Grant C (𝓛:Filter (ℕ×ℕ)) t)
open Zn
variable {d:ℕ}{Z:Arch C}(hz:steep 𝓛 Z)
open Finset StressFlux
local notation "Fᵣ"=> C.labels.level 4
local notation "Zᵣ"=> C.labels.level 5
abbrev taxA (Y:Levels G):= AgeK Y (1/5)
abbrev coin4(k:ℕ)(p:ℕ×ℕ)(t:Tickets C)(i:Bend):= fun a b=> MintC (Pick t i a b) 4 k p
abbrev coin5(k:ℕ)(p:ℕ×ℕ)(t:Tickets C)(i:Bend):= fun a=> MintC (PeakG t i a) 5 k p
-- budget poll all exact photos
include hu h
lemma article (i:Bend)(ε:ℝ)(hε:0 < ε) : ∀ᶠ k in atTop,∀ᶠ p:ℕ×ℕ in b!, ∃ w: Fin 3→ℝ, ‖w-BornZ i‖≤ ε ∧ OrbitT (Fᵣ) (coin4 k p t i)=BillC (Fᵣ) w∧ OrbitR (Zᵣ) (coin5 k p t i)=Vivid (Zᵣ) w∧rho h (bareVector w)=rho h (bareVector (BornZ i)):=by
    filter_upwards [hu,(hrate A h).eventually (pages (Fᵣ) (Zᵣ) C.params h _ hε)] with k hK hp;filter_upwards [hK] with p hk; let X:= rally t i k p.1 p.2; let J:= t k p.1 p.2|>.J; let R:= C.path.rep p.1 p.2 k; let F:= (Fᵣ); let H:=C.params; let Z:=(Zᵣ); let x:= (H! k); let n:= C.side k p.2
    have ht:20*(high x+10)< n.val:=by have he:= hk.site; change 20*(high x+rim x+10)< n.val at he; omega
    have hN:5 ≤ R.p.order:= le_trans (by norm_num:5≤6) R.p.order_ge; have hU:=reachBW hk
    have hs(w)(ht:Walt F Z H x X w): OrbitT (Fᵣ) (coin4 k p t i)=BillC (Fᵣ) w∧ OrbitR (Zᵣ) (coin5 k p t i)= Vivid (Zᵣ) w:=by
       refine ⟨funext fun a=> funext (ht.truth a),?_⟩; apply (plate Z).injective; rw[Vivid,show plate Z ( (plate (Zᵣ)).symm _)=_ from (plate Z).apply_symm_apply _]; apply Subtype.ext; funext a; change Z.coords.symm (OrbitR (Zᵣ) (coin5 k p t i)|>.val a)=_; apply Z.coords.injective;rw[LinearEquiv.apply_symm_apply]; exact ht.tempo a
    cases i with
    | some b=>
      let H' := hs _ (astra h b ht (hk.bases b) hN hU)
      exact ⟨azure b,by simp[BornZ,hε.le],H'.1,H'.2,rfl⟩
    | none=>
      obtain ⟨w,hW,h₀⟩:=Ponting (F:=F) (Z:=Z) (H:=C.params) hk.sea hN hU (by change 40≤n.val; omega) h
      have hg := hp n 0 J R w hk.sea.club hk.film ht hU hW; have he:=hs _ hW
      have hu:rho h (bareVector (BornZ none))=0:=by change rho h (bareVector (-tribe))=_; rw [map_neg,map_neg,rho_vector];norm_num[tribe]
      exact ⟨w,by simpa only[show BornZ none= -tribe from rfl,sub_neg_eq_add] using hg.le,he.1,he.2,h₀.trans hu.symm⟩
variable {i:Bend}{L:PaceBook C}(hV:Rod t i (𝓛:Filter (ℕ×ℕ)) L)
def Shine4 (Z:Arch C)(L:PaceBook C) (k:ℕ):= OrbitT (Fᵣ) (fun a b=> hence Z (L.T a b) k)
def Shine5 (Z:Arch C)(t:Axis→ Logs C 5)(k:ℕ):= OrbitR (Zᵣ) (fun a=> hence Z (t a) k)
def Road(k:ℕ)(p:ℕ×ℕ)(L:PaceBook C):= fun a b=> brevi (L.T a b) k p
def Roll(k:ℕ)(p:ℕ×ℕ)(v:Axis→ Logs C 5):= fun a=> brevi (v a) k p
include P hb hV
lemma roofs :∀ᶠ k in atTop,∀ᶠ p:ℕ×ℕ in b!, ‖Road k p L - coin4 k p t i‖ ≤ loss (A) k∧ ‖Roll k p L.Z - coin5 k p t i‖≤ loss (A) k:=by
   have he:= eager hu i; have hZ(x y):= tally P h hb hu (q:=Pick t i x y) (he.mono fun i h=> h.mono fun p ht=>ht.peek x y) (by omega) (hV.pole x y)
   have h'(x):= tally P h hb hu (q:=PeakG t i x) (he.mono fun i h=> h.mono fun p ht=>ht.full x) (by omega) (hV.bend x)
   filter_upwards [eventually_all.mpr fun x=> eventually_all.mpr fun y=>hZ x y, eventually_all.mpr h'] with k hk he; filter_upwards[eventually_all.mpr fun x=> eventually_all.mpr (hk x),eventually_all.mpr he] with p hp hu
   have he0:0 ≤ loss A k:= Zn.wake .. |>.le; refine ⟨(pi_norm_le_iff_of_nonneg he0).mpr fun x=>(pi_norm_le_iff_of_nonneg he0).mpr fun y=>hp x y,(pi_norm_le_iff_of_nonneg he0).mpr fun x=> hu x⟩
omit P hb hu h
include hz
lemma shipping : ∀ᶠ k in atTop,Tendsto (fun p:ℕ×ℕ=> OrbitT (Fᵣ) (Road k p L)) b! (𝓝 (Shine4 Z L k))∧ Tendsto (fun p:ℕ×ℕ=>OrbitR (Zᵣ) (Roll k p L.Z)) b! (𝓝 (Shine5 Z L.Z k)):=by
    filter_upwards [eventually_all.mpr fun a=> eventually_all.mpr fun b=>TravelsC.hi hz (v:= L.T a b) (hV.pole a b),eventually_all.mpr fun a=> TravelsC.hi hz (v:=L.Z a) (hV.bend a)] with k hk ht
    let U := fun a b=> hence Z (L.T a b) k; let T₁:=fun p:ℕ×ℕ=> Road k p L; let v:=fun a=> hence Z (L.Z a) k; have hh:Tendsto T₁ b! (𝓝 U):= tendsto_pi_nhds.mpr fun a=> tendsto_pi_nhds.mpr fun b=> hk a b
    exact ⟨(OrbitT (Fᵣ)|>.continuous.continuousAt).tendsto.comp hh, (OrbitR (Zᵣ)|>.continuous.continuousAt).tendsto.comp (show Tendsto (fun p:ℕ×ℕ=> Roll k p L.Z) b! (𝓝 v) from tendsto_pi_nhds.mpr ht)⟩
end YM.Trace.Slate
