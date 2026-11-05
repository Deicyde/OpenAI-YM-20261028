import YM.Extra.WILSON_STARTUP.Match
import YM.Extra.WILSON_STARTUP.TopStep
import YM.Next.FOUNDATIONS.SU2

/-!
# Changing just the boundary condition of Kin.Planned

All periods and depths; total choices even beyond N. No compatibility with
untold pricing/program invariants assumed. Replacement works if the revised
Horizon already overlaid and ready (separate obligation!). It leaves *lower*
α, station and paths as well as first-step α unchanged. Tag independence of
the prismatic branch equations is used only as established by F04's real
near-flat comparison, not for the full assigned-sector kernel.
-/
noncomputable section
set_option autoImplicit false
namespace YM.WilsonStartup.Change
open Function RG Wilson Lattice Bid Precision Exterior Bloch Tree Work Design
open scoped ContDiff Topology Matrix.Norms.Frobenius Classical
variable {G : Gauge} {a : Levels G} {M H : Horizon a} {O : ChartRatio G} {s : Supply.Sheet G} {D : Supply.Rolls s} {Q : PostCost D}

structure Overlay (M H : Horizon a) : Prop where
  peak N : M.H N N=bed (a.params N).clip
  other N m : m<N → M.H N m=H.H N m
  guesses N m : m<N → (M.towers N m).A0=(H.towers N m).A0

def revised (K : Kin H O) (N m : ℕ) := if m=N then top G (a.params N).clip else K.path N m

variable {K : Kin H O}

lemma top_match (h : K.Planned Q) (N p : ℕ) (hs : Suitable G (a.params N)) :
    Matches 4 (mainTerm (a.params N).clip (K.path N N) ∘ (represent (n:=a.S.side N p)))
              (mainTerm (a.params N).clip (revised K N N) ∘ represent) 0 := by
  rw [revised,if_pos rfl]
  refine ⟨(h.peak N p 0 (by decide)).1,(peak _ (n:=a.S.side N p) hs.direct 0 (by decide)).1,fun j hj =>
    ((h.peak N p j hj).2.2).trans ((peak _ hs.direct j hj).2.2).symm⟩

structure Stations (M : Horizon a) (K : Kin H O) {s : Supply.Sheet G} {D : Supply.Rolls s} (Q : PostCost D)
    (N m p : ℕ) (F : Forest (a.clock.op m p).ratio) (u : Dir G (a.S.side m p) → AxisChart G F) : Prop where
  gap : PriceGap F (a.params (m+1)).clip (revised K N (m+1)) (Q.η (a.clock.J (m+1)))
  critical : Critical F (a.params (m+1)).clip (revised K N (m+1)) u
  guess : Guessed F (installed (a.clock.op m p).ratio (M.towers N m).A0) u
  matchJet : ClassicalMatch F (a.params (m+1)).clip (a.params m).clip (revised K N (m+1)) (revised K N m) u
  wave : let j:= a.clock.J (m+1)
         FiniteBound F (revised K N (m+1)) (revised K N m) (a.params (m+1)).clip (a.params m).clip (K.alpha N m) O
            u (Q.Γ j) (Q.c j) (a.clock.loopCap (m+1))

lemma arrival (he : Overlay M H) (hO : LocalRatio O) (h : K.Planned Q) (N m p : ℕ) (hs : Suitable G (a.params N))
    (F : Forest (a.clock.op m p).ratio) (hm : m<N) :
    ∃ u, Stations M K Q N m p F u ∧ (m+1<N → u=K.stationary N m p F) := by
  obtain ⟨h₁,h₂⟩ := h.critical N m p hm F; have h₃ := h.classicalPart N m p hm F; have h₄ := h.retains N m p hm F
  have h₅ := h.gap N m p hm F
  rw [← he.guesses N m hm] at h₂
  by_cases hx : m+1=N
  · have hw : Matches 4 (mainTerm (a.params (m+1)).clip (K.path N (m+1)) ∘ (represent (n:=a.S.side (m+1) p)))
              (mainTerm (a.params (m+1)).clip (revised K N (m+1)) ∘ represent) 0 := by rw [hx]; exact top_match h N p hs
    obtain ⟨g,u,t,v,w,e⟩ := top_step hw (Q.price _) (a.blocks m p |>.branches) h₁ h₂ h₅ h₃ h₄ hO
      (fun b => by rw [hx]; exact h.initial N b) (by simp [revised,hx,top,extractAtom]; rfl)
    exact ⟨u, ⟨g,t,v,by rwa [show revised K N m = _ from if_neg hm.ne],by rwa [show revised K N m = _ from if_neg hm.ne]⟩,fun h => by omega⟩
  refine ⟨K.stationary N m p F,⟨?_,?_,h₂,?_,?_⟩,fun _ => rfl⟩ <;> simpa only [revised,if_neg hx,if_neg hm.ne]

theorem engine (he : Overlay M H) (hO : LocalRatio O) (h : K.Planned Q) (hs : ∀ N, Suitable G (a.params N)) :
    ∃ K' : Kin M O, K'.Planned Q ∧ K'.path=revised K ∧ K'.alpha=K.alpha ∧
      ∀ N m p F,m+1<N → K'.stationary N m p F = K.stationary N m p F := by
  have hv N m p (F : Forest (a.clock.op m p).ratio) : ∃ u, (m<N → Stations M K Q N m p F u) ∧
      (m+1<N → u=K.stationary N m p F) := by
    by_cases hm : m<N
    · obtain ⟨u,hh,h⟩ := arrival he hO h N m p (hs N) F hm; exact ⟨u,fun _ => hh,h⟩
    exact ⟨0,by simp [hm], by omega⟩
  choose f hf hr using hv
  let K' := Kin.mk (M:=M) (T:=O) K.alpha (revised K) f
  refine ⟨K',⟨h.stage,h.lengths,fun N m hm => ?_,fun N m hm => ?_,fun N p j hj => ?_,fun N b => ?_,
    fun N m p hm F => (hf N m p F hm).gap,fun N m p hm F => ⟨(hf N m p F hm).critical,(hf N m p F hm).guess⟩,
    fun N m p hm F => (hf N m p F hm).matchJet,h.kinetic,fun N m p hm F => (hf N m p F hm).wave⟩,rfl,rfl,hr⟩
  · change Attached _ (revised K N m); obtain hm|rfl := lt_or_eq_of_le hm
    · rw [he.other N m hm,revised,if_neg hm.ne]; exact h.links N m hm.le
    rw [he.peak,revised,if_pos rfl]; exact attached _
  · change (revised K N m).Bounds _ _ _ _; obtain hm|rfl := lt_or_eq_of_le hm
    · rw [revised,if_neg hm.ne]; exact h.cap N m hm.le
    rw [revised,if_pos rfl]; exact layout_ready (hs m)
  · simp only [K',revised,if_true]; exact peak _ (hs N).direct j hj
  simp [K',revised,top,extractAtom]; rfl
end YM.WilsonStartup.Change
