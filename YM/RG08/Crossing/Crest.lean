import YM.RG08.Crossing.Change
/-! # Absolute RG bills through one repeated program. L^-1/2 true
 smoothing gain, despite ranks 2,3,4 diagonal. -/
set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false
noncomputable section
namespace YM.RG08.Wings
open Filter Lattice Wilson Exterior Precision Laurent FreeResolvent Profiles Finset Function Next.Free RG Bloch Stationary Conductor Staffer Reflect UVExt.Paths Work.F08 Push.AbsoluteSums
open scoped BigOperators Topology Real Classical
variable {X : Chain} {G : Gauge} {K : KPrices X.kernel} {g : KGate K} {P : Lending G X.kernel} {E : ℕ} {S : Prism G X.kernel g P E} {ν : G.ColorIndex} {D : ChartRatio G}
variable {I : Type} {u : I→Windows} {r s e q : ℕ}

def LargeY (S : Prism G X.kernel g P E) (ν : G.ColorIndex) (D : ChartRatio G)(u : I→Windows)(e r : ℕ) :=
    Voucher (menu X (u:=u) (r:=0)) 1 (fun i=> moon X ν D i e r) (fun i=>Tier S i.i) ∧ Voucher (menu X (u:=u) (r:=1)) 1 (fun i=> lunar X ν D i e r) (fun i=>Tier S i.i)
lemma billUp (h : Circuit S ν D u){α:Type}{F:Wings u 0→ Shale α r}(he : Voucher (menu X) 1 F (fun i=>Tier S i.i)) : Voucher (menu X) 1 (fun t:Wings u 1=> F t.up) (fun i=>Tier S (i.i+1)) := (he.mold up).age (aged_up X h.M.crop) (sh X)
-- The Wilson column at top paid without consuming age there.
lemma launchQ (h : Circuit S ν D u) : Voucher (menu X (u:=u) (r:=0)) 1 (fun i=> Chain.column G X i.N i.N) (fun i=>Tier S i.i) := by
  have he b : Chain.column G X b b=caramel ν 2 := by unfold Chain.column Chain.K₀; rw [X.metric_wilson]; exact Eq.symm (caramel_two ..)
  simp_rw [he]
  obtain ⟨C,hC,H⟩:= sugar_paid (r:=2) ν zero_le_one
  exact ⟨_,Weighed.constant (menu X) hC,fun i=> by apply glow_less H (tiers S _) (by simp only [Pi.one_apply,mul_one,le_refl])⟩
private lemma growth (h : Circuit S ν D u)(hα : G.Simple)(hv : X.Wake G)(hp : LocalRatio D) {r q e : ℕ} (ha : e=r+2*q) (hk : 0<e)(he:e ≤ E)(hx : ∀ j p, RootStep 1 e (r+2) j p→ LargeY S ν D u j p) : Voucher (menu X) 1 (fun i:Wings u 0=> moon X ν D i e (r+2)) (fun i=>Tier S i.i) := by
  subst e
  have hE : r≤ E:= by omega
  let e := r+2*q; let c : Wings u 0→Pot G (r+2) := fun _=> wilsonTop ν e (r+2)
  let F i:= sector (orbit X i) (moon X ν D (i:Wings u 0)) q-sector (Chain.column G X i.N i.N) (wilsonTop ν) q
  let V i:= (F i (r+2)); have hy i: V i= moon X ν D i e (r+2)-c i := by unfold V F e c; simp only [Pi.sub_apply, sector, if_neg (Nat.ne_of_gt hk)]; rfl
  have hb t:= lyricsInk (rallies (ν:=ν) hv hp (t:Wings u 0)) (ralliedK hv hp (b:=t.N)) q
  have hP := launchCrop (u:=u) S ν e (r+2) 0
  obtain ⟨R,hR,H⟩:= coasting h hv hα hE (fun t=> F t.up) (fun i=> (hb i.up).1) (fun i=> (hb i.up).2) (δ:=1) (fun j hj=> billUp h (F:=fun i=>F i j) (smaller_sector (V:=orbit X) (U:=fun t=> Chain.column G X t.N t.N) (F:=moon X ν D) (H:=fun _=> wilsonTop ν) hα (fun i=>rallies hv hp i) (fun i=> ralliedK hv hp) ((q_right h).1.sub (launchQ h) (sh X)) (fun i j hj=> (show LargeY S ν D u _ _ from hx i j hj).1.sub (launchCrop (u:=u) S ν i j 0) (sh X)) hj))
  let U := single h hv
  have ht := duskBill h hv hp U rfl hk he (fun j p hj=> ⟨Both.self (billUp h (hx j p hj|>.1)),Both.self (hx j p hj|>.2)⟩) -- e,r parameters hidden.
  have hu: Presses X V 0 (Tier S) := by
    constructor
    · have ht i: V (roof i)=0 := by rw [hy]; unfold moon; rw [show (roof i).N=i.N from rfl,show (roof i).i=i.N from rfl,X.album_top]; exact sub_self _
      simp_rw [ht]; exact Voucher.zero
    refine ⟨R,?_,H⟩; rw [Wings.a_zero]
    let W i:= tilted X i ν (V i.up)
    let C i:= tilted X (i:Wings u 1) ν (c i.up)
    let B i:= dusk X (i:Wings u 1) ν D r q
    have hc : Voucher (menu X) 1 C (fun i=>Tier S i.i):=(tiltBill h U hE (F:=fun i=> c i.up) (Both.self (billUp h (F:=c) hP))).fresh
    rw [show _-_ = (W-R)+C+B-fun i=> c i.low from funext fun i=>?_]; · exact (((hR.plus hc (sh X)).plus ht.fresh (sh X)).sub (hP.mold low) (sh X)) -- ht issue
    have he : tilted X i ν (moon X ν D i.up e (r+2)) = W i+C i := by
      unfold W; rw [hy, tilt_sub hv _ ((rallies hv hp _).totes.1.2 _ _|>.2) (((top_gets ..).1.2 _ _).2)]; exact (sub_add_cancel ..).symm
    simp only [Pi.sub_apply, Pi.add_apply,hy]; rw [stepped hv hp i hk,he]; unfold B; abel -- `e` abbrev
  have ht := pathway X hu (show (0:ℝ)≤1/4 by norm_num); rw [a_zero] at ht
  rw [show (fun i=> moon X ν D i (r+2*q) (r+2))=(V+c) from funext fun i=> by rw [Pi.add_apply,hy]; exact (sub_add_cancel ..).symm ]; exact ht.plus hP (sh X)

lemma barren (hα : G.Simple)(hv : X.Wake G)(hp : LocalRatio D) (i : Wings u 0)(e) {r} (hr:r<2) : moon X ν D i e r=0 := by
    interval_cases r; exact (rallies hv hp i).totes.halt _; exact (rallies hv hp i).waxed hα _
private lemma cresting (h : Circuit S ν D u)(hα : G.Simple)(hv : X.Wake G)(hp : LocalRatio D)(he:e ≤ E) (hk : Played e r)(hx : ∀ j p, RootStep 1 e r j p→ LargeY S ν D u j p) : LargeY S ν D u e r := by
  obtain ⟨ha,q,hq⟩:= hk
  have ht : Voucher (menu X) 1 (fun i:Wings u 0=> moon X ν D i e r) (fun i=>Tier S i.i) := by
    by_cases hj:r<2
    · simp_rw [barren hα hv hp _ _ hj]; exact Voucher.zero
    obtain ⟨r,rfl⟩ : ∃ s,r=s+2:=⟨r-2,by omega⟩; exact growth h hα hv hp (q:=q) (by omega) ha he hx
  exact ⟨ht,(rawBill h (single h hv) hv hp he (by omega) (Both.self (billUp h ht)) (fun j p hj=> Both.self (billUp h (hx j p hj|>.1)))).fresh⟩

lemma root_ind (P : ℕ→ℕ→Prop) (he:e ≤ E)(hk:Played e r)(hx : ∀ e≤ E,∀ r,Played e r→(∀ j p,RootStep 1 e r j p→ P j p)→ P e r) : P e r := by
  induction e using Nat.strong_induction_on generalizing r with
  | h e IH=>
    have hr:r≤e+2:=by obtain ⟨h,q,hq⟩:=hk; omega
    generalize hx' : e+2-r=k
    induction k using Nat.strong_induction_on generalizing r with
    | h k ih=>
      apply hx e he r hk; rintro j p ⟨⟨hs,q,hq⟩,hj⟩
      by_cases hv : j=e
      · subst j; exact ih _ (by simp only [one_ne_zero,↓reduceIte] at hj; omega) (hk:=⟨hs,q,hq⟩) (by omega) rfl
      exact IH _ (by omega) (by omega) ⟨hs,q,hq⟩

lemma largest (h : Circuit S ν D u)(hα : G.Simple)(hv : X.Wake G)(hp : LocalRatio D)(he:e ≤ E) (r) : LargeY S ν D u e r := by
  by_cases ha: Played e r
  · exact root_ind _ he ha fun _ he _ ha=> cresting h hα hv hp he ha
  have hF i : moon X ν D (i:Wings u 0) e r=0 := not_ne_iff.mp (fun x=> ha ((rallies hv hp i).totes.1.1 _ _ x))
  have hH i : lunar X ν D (i:Wings u 1) e r=0 := not_ne_iff.mp (fun x=> ha ((X.rawStep ν D hv hp i.cut).1.1 _ _ x))
  unfold LargeY; simp_rw [hF,hH]; exact ⟨Voucher.zero,Voucher.zero⟩
end YM.RG08.Wings
