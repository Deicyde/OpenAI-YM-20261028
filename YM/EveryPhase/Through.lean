import YM.EveryPhase.Pure

/-! # Continue the jump RHS; uniform bounds extend to spectator neighborhoods -/
set_option autoImplicit false
noncomputable section
namespace YM.EveryPhase.Stress
open Function Set Filter MeasureTheory Metric Boundary Next.BOUNDARY Mink Complex Probe Table
open Work.C20 Next.BOUNDARY.Descent
open scoped Topology BigOperators
variable {G : Gauge} {L : Register G} {S U : Table L} {W : Surface S}
  {D : ∀ n, Blanket n} {Z : W.Aurora D} {P : DiffPlan S} {H : S.RealSpin} {F : Waves S} {n : ℕ}

def taskC (Z : W.Aurora D) (K : Killing) (R : S.Rotation) (P : DiffPlan S) (v : Fin n → S.Tag) (k : Fin (n+1))
    (t : S.Tag) (x : SpacePoints (n+1) × Times (n+1)) :=
    let y := laid x.1 x.2
    Z.emit (Bid.ink (hole k v ⟨t.1,rankAction R t.1 K.V t.2⟩)) y+∑ b : Axis,
      K.w b (fun a => y (k,a)) * Z.emit (Bid.ink (hole k v ⟨t.1+1,P.deriv t.1 b t.2⟩)) y
lemma task_pure (Z : W.Aurora D) (K : Killing) (R : S.Rotation) (P : DiffPlan S) (v : Fin n → S.Tag) (k : Fin (n+1))
    (t : S.Tag) (hF : F.Region U) (hZ : Z.FullBody F) (x : Points (n+1)) (hx : x∈ordered (n+1)) :
    taskC Z K R P v k t (pureDock x).1=taskE U K R P v x k t := by
  simp_rw [taskC,pureDock,pure_lay, K.w_wick, emit_root hF hZ _ hx]; rfl -- simp syntax

lemma neighborhoods {A : Type*} {B : Set ℂ} {L : Filter A} {R : A × ℂ → ℝ} {F : Set (A × ℂ)} (h : IsCompact B)
    (hk : ∀ x∈B, F∈L ×ˢ 𝓝 x ∧ ∃ C : ℝ, ∀ᶠ p in L ×ˢ 𝓝 x, R p ≤ C) :
    ∃ r>0, ∃ M : ℝ, ∀ᶠ a in L, ∀ z∈thickening r B, (a,z)∈F ∧ R (a,z)≤M := by
  have hh : {p : (ℝ × A) × ℂ| (p.1.2,p.2)∈F ∧ R (p.1.2,p.2)≤p.1.1} ∈ (atTop ×ˢ L) ×ˢ 𝓝ˢ B := by
    apply h.mem_prod_nhdsSet_of_forall
    intro y hy
    obtain ⟨T,M,hM⟩ := hk y hy
    have ht : Tendsto (fun z : (ℝ × A) × ℂ => (z.1.2,z.2)) ((atTop ×ˢ L) ×ˢ 𝓝 y) (L ×ˢ 𝓝 y) :=
      (tendsto_snd.comp tendsto_fst).prodMk tendsto_snd
    filter_upwards [ht.eventually hM,(tendsto_fst.comp tendsto_fst).eventually (eventually_ge_atTop M),ht T] with i hi hI hb
    exact ⟨hb,le_trans hi hI⟩
  obtain ⟨M,hM,T,hT,hh⟩ := mem_prod_iff.mp hh
  obtain ⟨C,hC,U,hU,u⟩ := mem_prod_iff.mp hM
  obtain ⟨p,hp⟩ := Filter.nonempty_of_mem hC
  obtain ⟨d,hd,hD⟩ := (hasBasis_nhdsSet_thickening h).mem_iff.mp hT
  refine ⟨d,hd,p,?_⟩; filter_upwards [hU] with x hx k hk
  exact hh (show ((p,x),k)∈M ×ˢ T from ⟨u ⟨hp,hx⟩, hD hk⟩)

lemma core_jump (K : Killing) (T : S.Stress) (v : Fin n → S.Tag) (k : Fin (n+1)) (B : S.Tag)
    (R : S.Rotation) (w : Prospect F Z U P H T) (h : StressLaws U T P.deriv R.lie)
    (g : Probe Space3) (hg : HasCompactSupport ⇑g) (hr : ∀ r, ((g r).re:ℂ)=g r)
    (p : Dock (n+1)) (hk : g =ᶠ[𝓝 (p.1.1 k)] fun _ => (1:ℂ)) (hu : p.1.2∈strict (n+1))
    (hs : allows p g k) (hh : atlases Z (sundial p k) k) :
    Tendsto (fun s => currentJump Z K T (Bid.ink (hole k v B)) g k ((p.1,0),s)) (𝓝[>] 0) (𝓝 (taskC Z K R P v k B p.1)) := by
  let u (z : ℂ) : Times (n+1) := fun i => ((p.1.2 i).im:ℂ)*I+z*((p.1.2 i).re:ℂ)
  have hd : Differentiable ℂ u := by unfold u; fun_prop
  let t (z) : Dock (n+1) := ((p.1.1,u z),0)
  let V := Bid.ink (hole k v B)
  let X (s : ℝ) (z : ℂ) := currentJump Z K T V g k (t z,s)
  let D (z) := taskC Z K R P v k B (t z).1
  have ht : Continuous t := ((continuous_const.prodMk hd.continuous).prodMk continuous_const)
  let E := ofReal '' Icc (0:ℝ) 1
  have he : IsCompact E := isCompact_Icc.image continuous_ofReal
  let J (p : ℝ × ℂ) := hole k.succ (u p.2) (morn (t p.2) k p.1)∈strict (n+2) ∧
    hole k.castSucc (u p.2) (eve (t p.2) k p.1)∈strict (n+2) ∧ u p.2 ∈ strict (n+1)
  obtain ⟨r,hr',M,hM⟩ := neighborhoods (F:= {p : ℝ × ℂ | J p}) (R:=fun p : ℝ × ℂ => ‖X p.1 p.2‖)
    (L:=𝓝[>] 0) he (by
      rintro z ⟨d,hh',rfl⟩
      let x := t d
      have hr (i : Fin (n+1)) : (x.1.2 i).im = (p.1.2 i).im := by simp [x,t,u]
      have hp : x.1.2 ∈ strict (n+1) := by intro i j ht; simp only [hr]; exact hu ht
      have hd : allows x g k := fun i r hr => lt_of_le_of_lt (by change |(0:ℝ)| ≤ |p.2|; simp [abs_nonneg]) (hs i r hr)
      have hv : atlases Z (sundial x k) k := by simp_rw [sundial,hr]; exact hh
      have hy : Tendsto (fun p : ℝ × ℂ => (t p.2,p.1)) (𝓝[>] 0 ×ˢ 𝓝 (d:ℂ)) ((𝓝 x) ×ˢ 𝓝[>] 0) :=
        ((ht.tendsto _).comp tendsto_snd).prodMk tendsto_fst
      obtain ⟨a,b,ha,hb⟩ := first_ports K T V k x hp hv w g hg hd
      refine ⟨?_,‖a-b‖+1,((ha.sub hb).comp hy).norm.eventually (ge_mem_nhds (by simp))⟩
      have hi := (show Continuous (fun i : Dock (n+1) => i.1.2) from by fun_prop).tendsto x
      filter_upwards [hy.eventually (affordable x hp k), (tendsto_fst.comp hy).eventually (hi.eventually ((open_strict (n+1)).mem_nhds hp))] with i hi hi'
      exact ⟨hi.1, hi.2, hi'⟩)
  let A := thickening r E
  obtain ⟨a,hA'⟩ := hM.exists
  have hA : IsOpen A := isOpen_thickening
  have hc : Convex ℝ E := (convex_Icc _ _).linear_image (ofRealCLM.toLinearMap)
  have hp : MapsTo u A (strict (n+1)) := fun p hp => (show J (a,p) from (hA' p hp).1).2.2
  have hX : ∀ᶠ s in 𝓝[>] (0:ℝ), DifferentiableOn ℂ (X s) A := by
    filter_upwards [hM] with s hs
    change DifferentiableOn ℂ (fun z => harbors Z K V T g k.succ p.1.1 (u z) (morn (t z) k s)-
      harbors Z K V T g k.castSucc p.1.1 (u z) (eve (t z) k s)) A
    apply DifferentiableOn.sub
    · refine harbors_hol A hA _ _ _ _ hd.differentiableOn ?_ (fun i hi => (show J (s,i) from (hs i hi).1).1) K V T g hg w.hZ
      dsimp only [morn,town,t]
      fun_prop
    refine harbors_hol A hA _ _ _ _ hd.differentiableOn ?_ (fun i hi => (show J (s,i) from (hs i hi).1).2.1) K V T g hg w.hZ
    dsimp only [eve,town,t]; fun_prop
  have hY : DifferentiableOn ℂ D A := by
    let y := fun z => laid p.1.1 (u z)
    have ha : MapsTo y A (tube (n+1)) := fun i hi => laid_inside _ (hp hi)
    have hv : Differentiable ℂ y := (laid_hol _).comp hd
    have he (v : Fin (n+1) → S.Union) : DifferentiableOn ℂ (fun z => Z.emit v (y z)) A :=
      (w.hZ.hol (n+1) v).differentiableOn.comp hv.differentiableOn ha
    dsimp only [D,taskC,t]; refine (he _).add (DifferentiableOn.fun_sum (fun b _ => ?_))
    have hc : Differentiable ℂ (fun z => K.w b (fun a => y z (k,a))) := fun z =>
      ((K.momentum b k (y z)).differentiableAt).comp z (hv z)
    exact hc.differentiableOn.mul (he _)
  have hz : (0:ℂ)∈A := self_subset_thickening hr' E ⟨0,⟨le_rfl,zero_le_one⟩,by simp⟩
  have h₁ : (1:ℂ)∈A := self_subset_thickening hr' E ⟨1,⟨zero_le_one,le_rfl⟩,by simp⟩
  have Hb (x) (hx : x∈A) : boundedHere X (𝓝[>] 0) x := by
    obtain ⟨l,hl,hL⟩ := Metric.mem_nhds_iff.mp (hA.mem_nhds hx)
    exact ⟨l,hl,M,hM.mono fun i hi z h => (hi z (hL h)).2⟩
  have hv : ∃ᶠ z in 𝓝[≠] (0:ℂ), z∈A ∧ Tendsto (fun a => X a z) (𝓝[>] 0) (𝓝 (D z)) := by
    let i (s : ℝ) := (s:ℂ)*I
    have he : Continuous i := by unfold i; fun_prop
    have hB : Tendsto i (𝓝[>] 0) (𝓝[≠] 0) := tendsto_nhdsWithin_iff.mpr ⟨by
      simpa [i] using (he.tendsto 0).mono_left (nhdsWithin_le_nhds (s:=Ioi 0)),
      (show ∀ᶠ s : ℝ in 𝓝[>] 0, 0<s from self_mem_nhdsWithin).mono (fun s hs => by simp [i,hs.ne'])⟩
    intro H
    obtain ⟨s,HH,hS⟩ := ((hB.eventually H).and ((hB.mono_right nhdsWithin_le_nhds).eventually (hA.mem_nhds hz))).exists
    apply HH; refine ⟨hS,?_⟩
    let x := place p.1.1 (fun k => (u (i s) k).im)
    have hu : pureU x=u (i s) := by
      funext a; apply Complex.ext <;> simp [pureU,x,u,i,place]
    have hz : Boundary.trace x=p.1.1 := by funext a; simp [Boundary.trace,x,place]
    have hC : t (i s)=pureDock x := by simp [pureDock,t,hz,hu]
    have hm : x∈ordered (n+1) := by
      intro i j hj; simp only [x,readings_place]; exact hp hS hj -- i shadow
    unfold X D; rw [hC,task_pure Z K R P v k B w.hF w.hZ x hm]
    refine pure_clock K T v x k hm B R w h g hg hr ?_
    exact show g =ᶠ[𝓝 (Boundary.trace x k)] _ from hz.symm ▸ hk
  have hh' := propagate_limit hA (hc.thickening r).isPreconnected hX hY Hb hz hv h₁
  have ht : t 1=(p.1,0) := by
    have hp : u 1=p.1.2 := by funext i; simp [u,add_comm]
    simp [t,hp]
  unfold X D at hh'; rw [ht] at hh'; exact hh'

/-- simultaneous limit, to simplify uniformity on test supports. -/
theorem through_jump (K : Killing) (T : S.Stress) (v : Fin n → S.Tag) (k : Fin (n+1)) (B : S.Tag)
    (R : S.Rotation) (w : Prospect F Z U P H T) (h : StressLaws U T P.deriv R.lie)
    (g : Probe Space3) (hg : HasCompactSupport ⇑g) (hr : ∀ r, ((g r).re:ℂ)=g r)
    (p : Dock (n+1)) (hk : g =ᶠ[𝓝 (p.1.1 k)] fun _ => (1:ℂ)) (hu : p.1.2∈strict (n+1))
    (hs : allows p g k) (hh : atlases Z (sundial p k) k) :
    Tendsto (currentJump Z K T (Bid.ink (hole k v B)) g k) (𝓝 p ×ˢ 𝓝[>] 0) (𝓝 (taskC Z K R P v k B p.1)) := by
  let A := currentJump Z K T (Bid.ink (hole k v B)) g k
  obtain ⟨a,b,ha,hb⟩ := first_ports K T (Bid.ink (hole k v B)) k p hu hh w g hg hs
  have ht : Tendsto A (𝓝 p ×ˢ 𝓝[>] 0) (𝓝 (a-b)) := ha.sub hb
  have he := core_jump K T v k B R w h g hg hr p hk hu hs hh
  have hw := variation K T (Bid.ink (hole k v B)) k p hu hh w g hg hs
  have hp : Tendsto (fun s => A (p,s)) (𝓝[>] 0) (𝓝 (taskC Z K R P v k B p.1)) := by
    simpa only [zero_add,sub_add_cancel] using hw.add he
  rw [tendsto_nhds_unique hp (ht.comp (tendsto_const_nhds.prodMk (tendsto_id (x := 𝓝[>] 0))))]; exact ht
end YM.EveryPhase.Stress
