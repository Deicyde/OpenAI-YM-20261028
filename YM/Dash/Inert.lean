import YM.Dash.Scope

/-!
# Candidate dossier into RawLimits over actual Wilson family

Upper null certificate before smooth, via
Raw.Scope. Matrices live prior to quotient. Do not extract unbounded
approximators for high derivatives: E estimate weighted by *same* x-u. Consumers expect compatible shapes along fixed f but may refine. Need such
certificates constructed from actual matches/budgets (red).
-/
set_option autoImplicit false
noncomputable section
namespace YM.Dash
open Function Set Filter MeasureTheory Complex Analysis Extraction
open scoped ContDiff Topology InnerProductSpace BigOperators
variable {G : Gauge} {C : Family G} {S : Table C.book} {f : Order} {d : ℕ}

abbrev snapshots (i : Shot C.book) (n : ℕ) (p : ℕ×ℕ) := i.scan n p.1 p.2

namespace Bin
variable (P : Bin S)

/-- silent projected candidate approximation (orthogonally Eq). -/
structure Upper (P : Bin S) (f : Order) (d : ℕ) : Prop where
  slides : Matrix P d f
  roots (i : Shot C.book) (x : C.label d) : Tendsto (fun u : ℕ×ℕ => snapshots i d u (x-(P d).step u x)) f.fuse (𝓝 0)

lemma quiet {h : Live S} (H : f.Ordered C S) (hs : Upper P f d) : LinearMap.ker (P d).trueP.toLinearMap ≤ monitor S h d := by
  intro x hx; rw [monitor, Submodule.mem_iInf]
  intro i; apply LinearMap.mem_ker.mpr
  have he : Tendsto (fun u : ℕ×ℕ => x-(P d).step u x) f.fuse (𝓝 x) := by
    have hx' := tendsto_const_nhds (x := x) (f := f.fuse) |>.sub (arcing hs.slides (tendsto_const_nhds (x := x)))
    rw [show (P d).trueP x=0 from hx, sub_zero] at hx'; exact hx'
  exact tendsto_nhds_unique (arcing (i.ready h H d) he) (hs.roots i x)

/-- Lower detector at d. Supply number comparison separately (projector
count from equations). Need every R test in monitor, not pair enough at
physical scale. -/
def shortage (H : Live S) (d) := Module.finrank ℂ (monitor S H d) ≤ Module.finrank ℂ (LinearMap.ker (P d).trueP.toLinearMap)

lemma exactC {h : Live S} (H : f.Ordered C S) (hs : Upper P f d) (hh : shortage P h d) : Good P h d :=
  Submodule.eq_of_le_of_finrank_le (quiet P H hs) hh

-- excludes hidden fit failure for tools
end Bin

/-- Gate to derivative: one test map ports, all s. balance in Shot includes
real signs. -/
abbrev TestPlan (P : Bin S) (f : Order) (d : ℕ) (_a : C.label d) (e : ℕ)
    (m : Shot C.book → ℂ) := ∃ x, Added m x (P e) f.fuse (fun i => snapshots i e)

def pushT (s : Shot C.book) (i : Axis) := {s with f:=down s.f s.i i}

/-- a in TestPlan type is for use markers; require all to avoid shadow altering estimates. -/
structure Spans (h : Live S) (P : Bin S) (f : Order) : Prop where
  p (d : ℕ) : P.Upper f d
  q (d : ℕ) : P.shortage h d
  /-- same terminal cylinder approximant across EVERY spectator. -/
  r (d e : ℕ) : d ≤ e → ∀ a : C.label d, TestPlan P f d a e (fun i => i.core S h a)
  t (d : ℕ) (k : Axis) (a : C.label d) : TestPlan P f d a (d+1) (fun i => - (pushT i k).core S h a)


structure MonitorOps (C : Family G) where
  keep {d e : ℕ} : d≤e → C.label d→ₗ[ℂ] C.label e
  tilt (d : ℕ) (a : Axis) : C.label d→ₗ[ℂ] C.label (d+1)

structure MonitorOps.Wakes (Y : MonitorOps C) (S : Table C.book) (h : Live S) : Prop where
  keep d e (hx : d≤e) (p : C.label d) (i : Shot C.book) : i.core S h (Y.keep hx p)=i.core S h p
  tilt d a (p : C.label d) (i : Shot C.book) : i.core S h (Y.tilt d a p)=-(pushT i a).core S h p

lemma lifts_model (h : Live S) (H : f.Ordered C S) (P : Bin S) (hm : Spans h P f) : ∃ Y : MonitorOps C, Y.Wakes S h := by
  have he d := Bin.exactC P H (hm.p d) (hm.q d)
  have ht {d e p m} (hc : TestPlan P f d p e m) : ∃ b : C.label e, ∀ i : Shot C.book, i.core S h b=m i := by
    obtain ⟨x,hx⟩ := hc
    obtain ⟨b,-,hb⟩ := brace (fun i => snapshots i e) (fun i => Shot.core i S h) (hm.p _).slides (he e) (fun i => i.ready h H _) x hx
    exact ⟨b,hb⟩
  let Vs (d) := Module.finBasis ℂ (C.label d)
  choose R hR using fun d e (hx : d≤e) i => ht (hm.r d e hx (Vs _ i))
  choose Q hQ using fun d a i => ht (hm.t d a (Vs _ i))
  let Y : MonitorOps C := ⟨fun {d e} p => (Vs d).constr ℂ (R d e p), fun p a => (Vs p).constr ℂ (Q p a)⟩
  have hb (d e) (p : d≤e) (i : Shot C.book) : (i.core (d:=e) S h).toLinearMap.comp (Y.keep p)=(i.core (d:=d) S h).toLinearMap := by
    apply (Vs d).ext; intro j
    simp only [Y, LinearMap.comp_apply, Module.Basis.constr_basis, ContinuousLinearMap.coe_coe,hR]
  have hx d a (i : Shot C.book) : (i.core S h).toLinearMap.comp (Y.tilt d a) = - ((pushT i a).core (d:=d) S h).toLinearMap := by
    apply (Vs d).ext; intro j
    simp only [Y, LinearMap.comp_apply,Module.Basis.constr_basis, ContinuousLinearMap.coe_coe,hQ,LinearMap.neg_apply]
  exact ⟨Y,fun d e w i p => LinearMap.congr_fun (hb _ _ w p) i,fun d a p i => LinearMap.congr_fun (hx d a i) p⟩

lemma MonitorOps.Wakes.through_ties {h : Live S} {Y : MonitorOps C} (H : Y.Wakes S h) : closeBy S := by
  intro n v i a
  refine ⟨update v i (⟨(v i).1+1,Y.tilt _ a (v i).2⟩ : C.book.Token),?_⟩
  intro f
  let s := Shot.mk n i v f
  have ht := H.tilt (v i).1 a (v i).2 s
  change f.applyTo (fun x => S.read x (s.record (d:=(v i).1+1) (Y.tilt _ a (v i).2))) = -(down f i a).applyTo (fun x => S.read x ((pushT s a).record (v i).2)) at ht
  rw [show (pushT s a).record (v i).2=v by unfold Shot.record pushT; simp [s]] at ht; exact ht

lemma sameWake {h : Live S} {T : Table C.book} {p : Live T} (hp : matchReg S T) {X : MonitorOps C}
    (he : X.Wakes S h) : X.Wakes T p := by
  have hw (i : Shot C.book) (d) (x : C.label d) : i.core (d:=d) S h x=i.core T p x := faithful hp _ _
  exact ⟨fun d e j a i => by rw [← hw i e,← hw,he.keep],fun d a v i => by rw [← hw i (d+1),← hw (pushT i a),he.tilt]⟩
end YM.Dash
