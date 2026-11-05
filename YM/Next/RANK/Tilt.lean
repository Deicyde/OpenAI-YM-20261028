import YM.Next.RANK.Breeze
import YM.Next.RANK.Post

/-!
# Ready stamped probes

Output both origin Ritz & costs with same frame. -/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Rank.Ribbon
open Function Filter RG Thirst Baler Lattice Wilson MeasureTheory Relation Corona Value Glyph Marker Perch Vac.Numbers Alarm Station Cells Spindle Atlas Edition Normal LiftMark Rise Paint MvPolynomial
open scoped BigOperators Classical Topology Matrix.Norms.Frobenius ContDiff

variable {G : Gauge} (C : Family G) {N k p d D : ℕ}

-- Kinematic approval

def Hail (k p D : ℕ) (X : AtlasData G C.S p) :=
    let A:= C.path.levels;let s:=clim A k;let Q:=control X (k:=k) 0 (wood A k)
    (∀ h : 4*sizeQ C k≤wood C.path.levels k,Stamped (sizeQ C k) (wood A k) k X h)∧
      ∀ i j, ‖Q.cov i j‖ ≤ tin s D

structure StampDuty (k N p d D : ℕ) (Q : Rep G (C.side k p)) (q : ℕ) (X : AtlasData G C.S p) where
  r : 4*sizeQ C k≤ wood C.path.levels k
  W : C.label d→poly (slotC G (sizeQ C k))
  crystal x: Spirit (W x)
  duration x: totalDegree (W x) ≤ D
  weight x: coin (W x) ≤ Perch.bill 1 (clim C.path.levels k)*paid C d k N p x
  heater : Heater C k d
  head x : heater x=milk (control X (k:=k) 0 (wood C.path.levels k)) (rename (calls r) (W x))
  T : Module.End ℂ (C.label d)
  lights : Heating C k N p d D heater T
  coupon (t : C.label d) : Ticket t (scouts C k) k N p Q.p (⟨halo (q*Q.p.B) {0},halo_subset _ _ (Finset.mem_singleton_self _)⟩)
      (signet 0 (GaugeScale C k N p) (W t)) (Perch.bill (-(D:ℝ)) (clim C.path.levels k)*paid C d k N p t)

lemma forge (g : G.Simple) (h : C.Makes) (d D : ℕ) (hd : d≤D) : ∀ᶠ k in atTop, C.ref d≤ k →
    year C D k → D+1 ≤ (C.path.levels.params k).order → ∀ N p, k≤N → ∀ (Q : Rep G (C.side k p)) (q : ℕ),
      Q.p.threshold= Spindle.tau C.path.levels k→Q.p.B=walls (clim C.path.levels k) → 8 ≤ q →
        ∀ X : AtlasData G C.S p,Hail C k p D X→ Nonempty (StampDuty C k N p d D Q q X):= by
  obtain ⟨V⟩:= charts G
  obtain ⟨c,hc,hV⟩:= machine V D C h d
  filter_upwards [housing C d g h,kpc D C g h d,fusible V C c hc d D g h,prototype C c hc d D V g h hd, LiftMark.supports D C g h] with k hp hf hs hx ht hm he hr N p hN Q q h₁ h₂ h₃ X hX
  have U := hp.2 p N hN; let u:= sizeQ C k; let i:=scouts C k; let Y:= C.path.rep N p k
  have hl : Y.p= C.path.levels.budget k:= (h.wilson.represents N p k hN).vac
  obtain ⟨F,hF⟩:= hV k u p i N hm hN (hl ▸ hr)
  let W := raww C k N p d U.length F; let z:= pinHat C d k; let J:=C.path.levels; let E:=shadow C k p D c; let L:=furnace C F hp.1 U
  let S:= control X (k:=k) 0 (wood C.path.levels k)
  have hM:= hx hm he p N hN U hp.1 F X (hX.1 hp.1) hF
  obtain ⟨T,hT⟩:= hf N p hN X L hX.2 hM
  have hE : 0 ≤ E:= by unfold E shadow; positivity
  have hv (x):Spirit (W x) := framed h hm hN U hE hF x
  refine ⟨⟨hp.1,W,hv, fun x=>qualified U hE hF x, fun x=>required h hN hp.1 U S hM (ht N hN p|>.2.1) x, Wick X L, ?_,T,hT,?_⟩⟩
  · intro x; rw [show Wick X L x=milk S (L x) from rfl, show L x= _ from carried h hN hp.1 U (F:=F) x]
  intro t; let P:=halo (q*Q.p.B) ({0}:Support (C.side k p))
  have he': Spindle.patch (n:=C.side k p) u 0⊆P:= by
    unfold Spindle.patch P;apply halo_mono _ le_rfl; unfold u sizeQ; rw [h₂]; gcongr
  have hP:=origin0 (W t) (hv t) (GaugeScale C k N p) (n:=C.side k p) 0
  refine ⟨⟨fun i=> (Provision.contained (h:=h) (hk:=hm) (hN:=hN) U t i).trans he'⟩,⟨hP.inv,hP.meas,fun U V h=> hP.locally _ _ (agrees_mono h (fun _ hx=> he' hx))⟩,fun u h'=>?_⟩
  exact hs N hN p hm he t _ (hF _) U u (h₁ ▸ Disjoint.mono_left he' h')

lemma StampDuty.procure (h : G.Simple) (H : C.Makes) (d D : ℕ) (v : C.label d) (b : ℝ) (hb : 0<b) (y : ℝ) (hi : y+b*d+saves C d ≤ -8): ∀ᶠ k in atTop,
    year C D k → ∀ N (p : ℕ), k ≤ N → ∀ {Q q X} (F : StampDuty C k N p d D Q q X), ∀ t,
        Price.Solves C (Station.mag C.path.levels b k) d k N p F.T v t →
        let s:= clim C.path.levels k;let E:=b*d+saves C d;let r:= Perch.bill y s
        r * moneys C d k N p t ≤ Perch.bill (-8) s ∧ coin (F.W t) ≤ Perch.bill E s := by
  filter_upwards [Atlas.income b hb h H v] with k hp hy N p hN Q q X F t hv s E r
  have h':= hp N p hN F.T F.lights.span t hv
  let A:= C.path.levels;rw [fire_bill] at h'; let u:= paid C d k N p t
  change bill 1 s * u ≤ Perch.bill E s at h'
  have hh:(A.params k).columns ≤ bill 1 s:= le_trans hy (Glimmer.billed _ (show LiftMark.shade D/4≤1 by linarith only [shaded D]))
  have he : u≥0:=paid_pos ..
  refine ⟨(mul_le_mul_of_nonneg_left (le_trans (mul_le_mul_of_nonneg_right hh he) h') (show 0≤r from Real.exp_pos _|>.le)).trans ?_, (F.weight _).trans h'⟩; unfold r; rw [overlap]; exact Glimmer.billed s (by unfold E; linarith only [hi])
end YM.Next.Rank.Ribbon
