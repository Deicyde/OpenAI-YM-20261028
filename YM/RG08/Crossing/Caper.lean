import YM.RG08.Crossing.Crest
/-! # Paired rate, solved iteration. Two histories same smoothing scheme &
levels, cutoffs arbitrary. Use absolute payment then only operation on ONE
representative, ∆-reset covered by absolute motion fees. Uniform all indices
in announced Circuit. No denominator WARD for physical used.
-/
set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false
noncomputable section
namespace YM.RG08.Wings
open Filter Lattice Wilson Exterior Precision Laurent FreeResolvent Profiles Finset Function Next.Free RG Bloch Stationary Conductor Staffer Reflect UVExt.Paths Work.F08 Push.AbsoluteSums
open scoped BigOperators Topology Real Classical
variable {X : Chain} {G : Gauge} {K : KPrices X.kernel} {g : KGate K} {P : Lending G X.kernel} {E : ℕ} {S : Prism G X.kernel g P E} {ν : G.ColorIndex} {D : ChartRatio G}
variable {I : Type} {u : I→Windows} {r s e q : ℕ}

structure Sliding (S : Prism G X.kernel g P E)(ν : G.ColorIndex)(D : ChartRatio G)(u:I→Windows)(e r : ℕ) : Prop where
    top : Both (menu X) (chop X (1/4)) (fun i:Wings u 0=> moon X ν D i e r) (fun i=> moon X ν D i.wingR e r) (fun i=>Tier S i.i)
    pre : Both (menu X) (chop X (1/4)) (fun i:Wings u 1=> lunar X ν D i e r) (fun i=> lunar X ν D i.wingR e r) (fun i=>Tier S i.i)

lemma bothUp (h : Circuit S ν D u) {F H:Wings u 0→Pot G r} (he : Both (menu X) (chop X (1/4)) F H (fun i=> Tier S i.i)) : Both (menu X) (chop X (1/4)) (fun i:Wings u 1=> F i.up) (fun i=> H i.up) (fun i=> Tier S (i.i+1)) := ⟨billUp h he.fresh,billUp h he.again,receipt X h.M.crop (by norm_num) he.moves⟩
private lemma peak (h : Circuit S ν D u)(hα : G.Simple)(hv : X.Wake G)(hp : LocalRatio D) (ha:e=r+2*q) (hk:0<e)(he:e ≤ E)(hx : ∀ j p, RootStep 1 e (r+2) j p→ Sliding S ν D u j p) : Both (menu X) (chop X (1/4))
    (fun i:Wings u 0=> moon X ν D i e (r+2)) (fun i=>moon X ν D i.wingR e (r+2)) (fun i=>Tier S i.i) := by
  subst e
  let e:=r+2*q
  have hE : r ≤ E:=by omega -- e occur?
  let μ:=chop X (r:=0) (u:=u) (1/4); let δ:=chop X (u:=u) (r:=1) (1/4)
  have hA:= (largest h hα hv hp he (r+2)).1; have hy := hA.mold wingR
  refine ⟨hA,hy,?_⟩
  let F i:= sector (orbit X i) (moon X ν D (i:Wings u 0)) q-sector (orbit X i.wingR) (moon X ν D i.wingR) q
  let V i:= F i (r+2); have hy' i: V i= moon X ν D i e (r+2)-moon X ν D i.wingR e (r+2) := by unfold V F; simp only [Pi.sub_apply,sector,if_neg (Nat.ne_of_gt hk)]; rfl
  have hb t:= lyricsInk (rallies (ν:=ν) hv hp (t:Wings u 0)) (rallies (ν:=ν) hv hp t.wingR) q
  have hR j (hj:j<r+2) : Voucher (menu X) μ (fun i=> F i j) (fun i=> Tier S i.i) := smaller_sector (H:=fun i:Wings u 0=>moon X ν D i.wingR) (F:=moon X ν D) (U:=fun i=>orbit X i.wingR) (ν:=ν) hα (fun i=> rallies hv hp i) (fun i=>rallies hv hp i.wingR) (q_right h).moves (fun i j hj=>(hx i j hj).top.moves) hj
  obtain ⟨R,hR,H⟩:= coasting h hv hα hE (fun t=> F t.up) (fun i=> (hb i.up).1) (fun i=> (hb i.up).2) (δ:=δ) (fun j hj=> receipt X h.M.crop (by norm_num) (hR j hj))
  have hC:= duskBill h hv hp (doubleL h hv) rfl hk he (fun j p hj=> ⟨bothUp h (hx j p hj|>.top),hx j p hj|>.pre⟩)
  rw [show _-_ = V from funext fun i=> (hy' i).symm]; refine pathway X ⟨?_,R,?_,H⟩ (by norm_num)
  · simp_rw [hy']; exact (hA.mold roof).sub (show Voucher _ _ _ _ from (show Voucher (menu X) 1 _ _ from hy).mold roof) fun i=> sh X _
  let C i:= tilted X (i:Wings u 1) ν (V i.up)
  let B (t:Wings u 1):= moon X ν D (wingR (up t)) e (r+2)
  let T i:= tilted X (i:Wings u 1) ν (B i)-tilted X i.wingR ν (B i)
  have he : Voucher (menu X) δ T (fun i=>Tier S i.i):=(tiltBill h (doubleL h hv) hE (F:=B) (Both.self (billUp h (show Voucher (menu X) 1 _ _ from hy)))).moves
  rw [show _-_ = ((C-R)+T)+fun i=>dusk X i ν D r q-dusk X i.wingR ν D r q from funext fun i=>?_]; · exact ((hR.plus he (sh X)).plus hC.moves (sh X))
  have hw i' := ((rallies (ν:=ν) hv hp (i':Wings u 0)).totes.1.2 e (r+2)).2
  have hj' : moon X ν D i.low.wingR (r+2*q) (r+2)= tilted X i.wingR ν (B i)+dusk X i.wingR ν D r q:=stepped hv hp i.wingR hk
  have hs := hy' i.low; dsimp only [e] at hs
  simp only [C,T,Pi.sub_apply,Pi.add_apply,hs]; rw [stepped hv hp i hk,hj',hy', tilt_sub hv _ (hw _) (hw _)]; unfold B e; abel
private lemma skied (h : Circuit S ν D u)(hα : G.Simple)(hv : X.Wake G)(hp : LocalRatio D)(he : e ≤ E) (hk : Played e r) (hx : ∀ j p, RootStep 1 e r j p → Sliding S ν D u j p) : Sliding S ν D u e r := by
    obtain ⟨hh,q,hq⟩:=hk
    have he' : Both (menu X) (chop X (1/4)) (fun i:Wings u 0=> moon X ν D i e r) (fun i=>moon X ν D i.wingR e r) (fun i=>Tier S i.i) := by
      by_cases hp' : r<2
      · simp_rw [barren hα hv hp _ _ hp']; exact Both.zero
      obtain ⟨r,rfl⟩ : ∃ s,r=s+2:=⟨r-2,by omega⟩; exact peak h hα hv hp (q:=q) (by omega) hh he hx
    exact ⟨he',(rawBill h (doubleL h hv) hv hp he (by omega) (bothUp h he') fun j p hj=> bothUp h (hx j p hj).top)⟩

theorem skater (h : Circuit S ν D u)(hα : G.Simple)(hv : X.Wake G)(hp : LocalRatio D)(he : e ≤ E) (r) : Sliding S ν D u e r := by
  by_cases ha: Played e r; · exact root_ind _ he ha fun _ he _ ha=> skied h hα hv hp he ha
  have hF i : moon X ν D (i:Wings u 0) e r=0 := not_ne_iff.mp (fun x=> ha ((rallies hv hp i).totes.1.1 _ _ x))
  have hH i : lunar X ν D (i:Wings u 1) e r=0 := not_ne_iff.mp (fun x=> ha ((X.rawStep ν D hv hp i.cut).1.1 _ _ x))
  constructor; · simp_rw [hF]; exact Both.zero
  simp_rw [hH]; exact Both.zero
end YM.RG08.Wings
