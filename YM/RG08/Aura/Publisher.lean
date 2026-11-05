import YM.RG08.Yamen.Crown
import YM.Planned.PRIMARY_INTEGRAL_295.RollFilm

/-! # Independent quadratic solver for reading the fine / coarse shift on marks.
 Shares ERA geometry & toll, does not presume H of the consumer uses same stochastic tower.
-/
noncomputable section
namespace YM.RG08.Aura
open Lattice Laurent Pert.Bulk Forms Room Carrel Steam Rate Stair RG Stationary Bloch Rudder RG08.Mount Tack Anchor Spar Sedan Precision Finset Exterior Nacre PowerSeries Finset.Nat Symmetry Prism Quarry Roost Packets Ducat Mason Yamen Rows Filter Flat
open YM.Next.Free YM.Planned.PrimaryIntegral295
open scoped Classical Matrix BigOperators PowerSeries Topology
set_option autoImplicit false
variable {G:Gauge}

private lemma flying_shadow (a:Levels G)(p:ℕ→ℝ)(h:∀ i,0<p i)(i t): flying (Flat.shadow a p h) t i=flying a t i:=by
 induction t generalizing i with
 | zero=>rfl
 | succ k hi=>unfold flying;rw [hi (i+1)];rfl

private lemma shipShadow (a:Levels G)(p:ℕ→ℝ)(h:∀ i,0<p i)(N i): destination (Flat.shadow a p h) N i=destination a N i:=by unfold destination location; rw [flying_shadow];rfl
/-- Expose only the universal quadratic tower program, at all periods. Don't ask downstream to
 switch trajectories even locally: `Inputs` evaluated with THEIR given Horizon, by same embedded
 Hessian (works for choosing future lifts, interfaces, etc). Consumption of d0 not d2. -/
def licensed (a:Levels G)(H:Horizon a):Prop:=∀ N m n,m < N→
 let S:= a.clock.op m n ;let W:=installed S.ratio (Carrier.linesOf (destination a N m) a.clock.kernel.penalty)
 ; Inputs S W ((H.H N (m+1)).metric.acts _) ((H.H N m).metric.acts _)

theorem dual_support (G:Gauge)(s:Supply.Sheet G):∃ b:ℕ→ℕ,∀ a:Levels G,a.clock.kernel=s.kernel→a.clock.stage=s.profile→ (∀ i,b (a.clock.J (i+1)) ≤ (a.S.block i).val)→∀ (H:Horizon a){P:MapPrices}, H.Suffices P→ licensed a H:=by
 obtain ⟨X,l,γ,b,h,hT⟩:= retained_support (G:=G) s.kernel
 let f:Supply.Sheet G:= {s with profile:=fun i=>Flat.rearrange (s.profile i) (γ i) (h.fit i)}
 obtain ⟨T,H⟩:= hT f rfl
 refine ⟨b,fun a ha hs hd A P hP=>?_⟩
 let c:= Flat.shadow a γ h.fit
 obtain ⟨_,Y,_,_,_,he,hQ,_⟩:=H c ha (funext fun i=>by unfold c Flat.shadow Flat.adjust f;simp only [hs]) ⟨fun _=>le_rfl, hd⟩
 intro N m n hm
 have hx(i)(hv:i ≤ N):output (A.H N i)=output (Y.H N i):= Flat.same_shadow a γ h.fit hP he N i hv
 have hX(i)(hi:i ≤ N)(n) : Precision.K ((A.H N i).metric.acts n)=Precision.K ((Y.H N i).metric.acts n):=by
    have ht{a:Levels G}(A:Horizon a){P:MapPrices}(h:A.Suffices P): Matches (output (A.H N i)) (quadratic (A.H N i) n):=(output_cost (σ:=0) (fun x y=> ((h.rows N i hi).2.1 x y).mono (P.alpha_pos _).le le_rfl) (Ω_pos h i) (le_refl _) zero_le_one).2 n
    -- defer hole
    ext ⟨x,a'⟩ u :1
    have H1:=ht A hP ((lift x,a'):Market _) u;have H2:=ht Y he ((lift x,a'):Market _) u
    rw [hx i hi] at H1; dsimp only at H1 H2
    erw [wrap_lift] at H1 H2
    exact H1.symm.trans H2
 intro S W
 obtain ⟨hf,h2⟩:= hQ.2 N m hm
 let W':=installed S.ratio (Y.towers N m).A0
 have hb : Inputs S W' ((Y.H N (m+1)).metric.acts _) ((Y.H N m).metric.acts _):=(he.crossings N m n hm).trial
 have hw : W=W':=by unfold W Carrier.linesOf W'; rw [hf]; apply congrArg (fun T:Carrier.Lines S.ratio.count=> installed S.ratio T); apply eq_of_heq; refine (show ∀ i j:Flight (a.clock.J (m+1)) (a.clock.J m),i=j→HEq ((Flight.duo a.clock.kernel.penalty i).A0) ((Flight.duo a.clock.kernel.penalty j).A0) from fun i j h=> by subst i;exact HEq.rfl) _ _ ((shipShadow a γ h.fit N m).symm) -- exact (shipShadow a γ h.fit N m).symm
 constructor <;> rw [hw, hX m hm.le _] -- binder
 · rw [hX _ hm _]; exact hb.primal
 exact hb.dual
end YM.RG08.Aura
