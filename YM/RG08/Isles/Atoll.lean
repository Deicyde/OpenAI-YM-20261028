import YM.RG08.Isles.Pieces

noncomputable section
namespace YM.RG08.Isles
open Forms Pert.Bulk Packets Laurent Finset Function Lattice Filter
open scoped Topology BigOperators ENNReal Classical
set_option autoImplicit false
variable {I:Type} {n p:ℕ}{σ C B W:ℝ}{F:Flake (n+1) (Market I)}{f:ViewDeck (n+1) I}{g:(i:ℕ)→Line (colony I i)}{Γ:Line (Market I)}

private lemma fountain (h:Study σ C f F)(H:StudyLine σ W g Γ)(m:ℕ)(x:Tape n (Market I))(i:Fin n)(u v:colony I m):
   |f m (Fin.cons u ((carpetRoad I).visit m ∘ x))| * |g m u v| ≤ C*W*Real.exp (σ*abroad (x i))*(weightU (σ/2) (reach u)*weightU (σ/2) (reach v)) := by
 apply (mul_le_mul (h.basis m _ (x i) i.succ 0 (by simp [carpetRoad])) (H.point m u v) (abs_nonneg _) (by have:=h.cost;positivity)).trans
 rw [Fin.cons_zero]
 unfold weightU;rw [here,here,←Real.exp_add]
 let t:= σ*abroad (x i)
 let e:=(shore (chain m) I).span u v
 change (C*Real.exp t*Real.exp (-σ*native u))*(W*Real.exp (-σ*e))≤C*W*Real.exp t*_
 calc
 _ = C*W*Real.exp t*Real.exp ((-σ*native u)+(-σ*e)):=by rw [Real.exp_add]; ring
 _ ≤ _:=by
     have he:=h.cost;have hb:=H.palm.gain
     have hv:native v≤e+native u:=by simpa only [(shore (chain m) I).left v] using (region v u)
     have ht: 0≤e:= (shore (chain m) I).nn ..
     apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by positivity);nlinarith [h.rate]

variable {G:Flake (p+1) (Market I)}{k:ViewDeck (p+1) I}

private lemma fact (h:Study σ C f F)(hG:Study σ B k G)(H:StudyLine σ W g Γ)(m:ℕ)(x:Tape n (Market I))(y:Tape p (Market I))(i:Fin n)(u v:colony I m):
  ‖seam (g m) (f m) (k m) (Fin.append ((carpetRoad I).visit m ∘ x) ((carpetRoad I).visit m ∘ y)) (u,v)‖≤(C*W*B*Real.exp (σ*abroad (x i)))*(weightU (σ/2) (reach u)*weightU (σ/2) (reach v)):=by
 rw [seam_tool,Real.norm_eq_abs,abs_mul,abs_mul]
 apply (mul_le_mul (fountain h H m x i u v) ((hG.calm m).plain hG.cost hG.rate.le (by omega) _) (abs_nonneg _) (by unfold weightU;have:=H.palm.gain;have:=h.cost;positivity)).trans_eq
 ring

private lemma passage (h:Study σ C f F)(hG:Study σ B k G)(H:StudyLine σ W g Γ)(x:Tape n (Market I))(y:Tape p (Market I))(a:Market I× Market I):
 Tendsto (fun m=>seam (g m) (f m) (k m) (Fin.append ((carpetRoad I).visit m ∘ x) ((carpetRoad I).visit m ∘ y)) (port (chain m) a.1,port (chain m) a.2)) atTop (𝓝 (seam Γ F G (Fin.append x y) a)):=by
 obtain ⟨u,v⟩:=a
 simp_rw [seam_tool]; refine Tendsto.mul (Tendsto.mul ?_ (H.light u v)) ?_
 · convert h.light (by omega) (Fin.cons u x) using 2
   congr 2; ext j:1;cases j using Fin.cases <;> rfl
 convert hG.light (by omega) (Fin.cons v y) using 2
 congr 2; ext j:1;cases j using Fin.cases<;>rfl

variable [Fintype I]
private lemma seeing (h:Study σ C f F)(hG:Study σ B k G)(H:StudyLine σ W g Γ)(x:Tape n (Market I))(y:Tape p (Market I))(hn:0<n+p):
    Tendsto (fun m=>weld (g m) (f m) (k m) ((carpetRoad I).visit m ∘ Fin.append x y)) atTop (𝓝 (weld Γ F G (Fin.append x y))):=by
 have he (m:ℕ): (carpetRoad I).visit m ∘ Fin.append x y= Fin.append ((carpetRoad I).visit m ∘ x) ((carpetRoad I).visit m ∘ y):=by ext j:1; cases j using Fin.addCases <;> simp
 simp_rw [he,weld]
 let R:=(carpetRoad I).prod (carpetRoad I)
 have hr(t):Summable (fun z : Market I × Market I=> t*(weightU (σ/2) z.1 * weightU (σ/2) z.2)):= (weightU_twice (by have he:=h.rate;linarith)).mul_left t
 by_cases hz:0<n
 · let i:Fin n:=⟨0,hz⟩
   let Q:=C*W*B*Real.exp (σ*abroad (x i));have hq:0≤Q:=by unfold Q;have he:=h.cost;have hw:=H.palm.gain;have hr:=hG.cost;positivity
   exact DCT R (fun m u=> seam (g m) (f m) (k m) _ u) _ _ (passage h hG H x y) (hr Q) (fun _=>by unfold weightU; positivity) (.of_forall (fun m ⟨u,v⟩=> fact h hG H m x y i u v))
 · let i:Fin p:=⟨0,by omega⟩
   let Q:=B*W*C*Real.exp (σ*abroad (y i));have hq:0≤Q:=by unfold Q;have he:=h.cost;have hw:=H.palm.gain;have hr:=hG.cost;positivity
   refine DCT R (fun m u=>seam (g m) (f m) (k m) _ u) _ _ (passage h hG H x y) (hr Q) (fun _=>by unfold weightU;positivity) (.of_forall fun m ⟨u,v⟩=> ?_)
   convert fact hG h H.turn m y x i v u using 1
   · rw [seam_tool,seam_tool]; unfold swap; ring_nf
   · dsimp [R,Route.prod,carpetRoad,Q];rw [mul_comm (weightU ..) (weightU ..)]

lemma Study.join (h:Study σ C f F)(hG:Study σ B k G)(H:StudyLine σ W g Γ) :
 Study σ (C*W*B) (fun m=>bridge (g m) (f m) (k m)) (bridge Γ F G):=by
 unfold bridge;apply Study.bleach
 refine ⟨h.rate,mul_nonneg (mul_nonneg h.cost H.palm.gain) hG.cost,h.palm.weld hG.palm H.palm h.cost hG.cost, fun m=>(h.calm m).weld (hG.calm m) (H.calm m) h.cost hG.cost,?_⟩
 intro hn z
 obtain ⟨⟨x,y⟩,rfl⟩: ∃ w,(Fin.appendEquiv (α:=Market I) n p w)=z:=(Fin.appendEquiv ..).surjective z
 exact seeing h hG H x y hn
end YM.RG08.Isles
