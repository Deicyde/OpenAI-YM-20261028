import YM.WilsonBulk.Slice.Siding

/-!
# Compatible representations of step kinetics and moments

Use Heat data on ambient coordinates with collapsed directions implicit.
Bridge to `Cradle` with private coords and shift (including reindexing
congruences allowed via matrix presentations).
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonBulk.Sheet
open scoped BigOperators Classical
open Finset Function PowerSeries Matrix
variable {α β ι κ A : Type} [Fintype α] [Fintype β] [Fintype κ] [Fintype ι]
variable {G : Matrix κ κ ℝ} {H : Matrix α α ℝ} {Y : Matrix α α ℝ} {K F : Matrix α α ℝ} {X : Matrix β α ℝ} {P : Matrix β β ℝ}
variable (A : Matrix α β ℝ) -- predictor abs log
variable (Q : Matrix α κ ℝ) -- private injection
variable (u : β→ Tape ι)
abbrev ambient (K : Matrix α α ℝ) (X : Matrix β α ℝ) (p : ℝ) := atelier K X p (fun i=> privateName (ι:=β) i) (fun i:β=>viewer i)
abbrev grains (P : Matrix β β ℝ) : Tape β := forceQ P named
variable {B : Matrix κ κ ℝ}
def seating (e : Chamber α β) : StageD κ ι := Sum.elim (quill Q privateName+ quill A (fun i=>boast κ ι (u i))) (fun i=> boast κ ι (u i)) e
section
omit [Fintype α] [Fintype ι]
lemma seeing (x : α) : seating A Q u (Sum.inl x)= quill Q privateName x +quill A (fun i=>boast κ ι (u i)) x := rfl
lemma seeing₂ (x : β) : seating A Q u (Sum.inr x)=boast κ ι (u x) := rfl
end
def ruling : StageD α β→ₐ[ℝ] Tape β := submit (Sum.elim (quill A named) named)
omit [Fintype α] in
lemma ruling_cons (x : α) : ruling A (privateName x)=quill A named x := submit_named ..
omit [Fintype α] in
lemma ruling_dst (x : β) : ruling A (viewer x)=named x := submit_named ..
-- root equality at coarse center
omit [Fintype α] in
lemma seating_reflect (h : Q*G*Q.transpose = H) : Reflects (seating A Q u) (forkM (ι:=β) (κ:=ι) Q) (house H) (house G) := by
  have he := facade_reflect u h
  refine ⟨fun i j hij=>?_,he.projects⟩
  -- restricted derivative
  rcases i with i|i; swap; exact False.elim (hij (house_front ..))
  rcases j with j|j; swap; exact False.elim (hij (house_out ..))
  have he (j:κ) (e : Chamber α β) : player (Sum.inl j) (seating A Q u e)=player (Sum.inl j) (facade Q u e) := by
    rcases e with a|b
    · rw [seeing, map_add,facade]; dsimp only [Sum.elim]; rw [add_eq_left]
      simp only [quill,map_sum,Derivation.map_smul, show ∀ i:β,player (Sum.inl j) (boast κ ι (u i))=0 from fun i=>hat_still .., smul_zero,sum_const_zero]
    rfl
  -- recover
  simp_rw [he]; exact (facade_reflect u h).underlies _ _ hij
lemma seats (f : StageD α β) (h : Q*G*Q.transpose=H) : bags ι G (submit (seating A Q u) f)=submit u (ruling A (parallel (wick (house H)) f)) := by
  rw [bags_script,(seating_reflect A Q u h).all]
  apply DFunLike.congr_fun (f:=(blankD κ ι).comp (submit (seating A Q u))) (g:=(submit u).comp (ruling A))
  apply code_ext
  · simp only [AlgHom.comp_apply,submit_X,blankD_X,constantCoeff_X]
  · simp only [AlgHom.comp_apply,submit_X,blankD_X,ruling]
  intro i; cases i with
  | inr i=> rw [AlgHom.comp_apply, submit_named,seeing₂,boast_home]; exact ((congr_arg (submit u) (ruling_dst A i)).trans (submit_named ..)).symm
  | inl i=> rw [AlgHom.comp_apply,AlgHom.comp_apply,submit_named,seeing, ruling,submit_named]; simp only [map_add,quill,map_sum,map_smul,blankD_name,boast_home, Sum.elim_inl,submit_named,smul_zero,sum_const_zero,zero_add]

variable (p : ℝ)
omit [Fintype ι] in
lemma ambient_substitute [DecidableEq β] (he : rear K X p=Y) (hv : Q.transpose*Y*Q=B) (hw : Y.IsSymm)
    (hx : Y*A=p • X.transpose) (hy : p • ((1:Matrix β β ℝ)- X*A)=P) : submit (seating A Q u) (ambient K X p)=boast κ ι (submit u (grains P))+seedQ ι B := by
  let x : α→ StageD κ ι :=quill Q privateName
  let y i:=boast κ ι (u i)
  have ha : (fun i:α=>submit (seating A Q u) (privateName i))=x+quill A y := funext fun i=> submit_named ..
  have hc : (fun i:β=> submit (seating A Q u) (viewer i))=y := funext fun i=> submit_named ..
  unfold ambient; rw [atelier_map,ha,hc]; unfold x y
  rw [atelier_bull A Y he.symm hw hx hy, force_transfer,hv,grains,forceQ_map,forceQ_map]; simp_rw [submit_named]; rw [add_comm]
-- V̂ insertion = centered pwr. Log meaning load equality ANY fixed-demand all orders if someone has FrameBound etc. No existence assumed.
omit [Fintype ι] in
abbrev curtain (K : Matrix α α ℝ) (X : Matrix β α ℝ) (p : ℝ) (F M : StageD α β) := -F+ambient K X p+ M
structure Scripts (H K : Matrix α α ℝ) (X : Matrix β α ℝ) (p : ℝ) (F M : StageD α β) (R : Tape β) : Prop where
  leading : Steps 1 F (ambient K X p)
  jac : constantCoeff M=0
  read : ruling A (parallel (wick (house H)) (tide (curtain K X p F M))) = tide R
  starts : constantCoeff R=0
variable {F' M : StageD α β} {R : Tape β}
omit [Fintype ι] in
lemma Scripts.empty (h : Scripts A H K X p F' M R) : constantCoeff (curtain K X p F' M)=0 := by unfold curtain; simp only [map_add,map_neg,(steps_initial ..).mp h.leading,h.jac]; abel
lemma Scripts.present (h : Scripts A H K X p F' M R) [DecidableEq β] (hc : Q*G*Q.transpose=H) (he : rear K X p=Y) (hv : Q.transpose*Y*Q=B) (hw : Y.IsSymm)
    (hx : Y*A=p • X.transpose) (hy : p • ((1:Matrix β β ℝ)- X*A)=P) :
    let U:= submit (seating A Q u); Cradle B G (U F') (U M) (U (curtain K X p F' M)) (submit u (grains P)) (submit u R) := by
  intro U; have ha : constantCoeff (U PowerSeries.X)=0:= by rw [show U PowerSeries.X=PowerSeries.X from submit_X _,constantCoeff_X] -- X shadows fix
  have hg : U (ambient K X p)= _ := ambient_substitute A Q u p he hv hw hx hy
  refine ⟨?_, c_empty U ha h.jac,?_, ?_,c_empty _ (by rw [submit_X,constantCoeff_X]) h.starts⟩
  · have h:=h.leading.push U ha; rwa [hg] at h
  · simp only [curtain,map_add,map_neg,hg]; abel
  rw [← show U (tide (curtain K X p F' M))=tide (U (curtain K X p F' M)) from tutor _ constantCoeff_X (h.empty A p)]; unfold U; rw [seats A Q u _ hc,h.read]; exact tutor _ constantCoeff_X h.starts
lemma script_ready {i : Record (Chamber α β)} (I : FrameBound i) (hI : Free i) (hA : Based i)
    (hz : constantCoeff M=0) (ht : Steps 1 F' (ambient K X p)) (he : volumeTape i=curtain K X p F' M) :
    Scripts A H K X p F' M (ruling A (volumeTape (receive (house H) i false))) := by
  have hr := (siteLimits (house H) false I hI hA).2.2
  have H' : constantCoeff (ruling A PowerSeries.X)=0 := by rw [ruling,submit_X,constantCoeff_X]
  refine ⟨ht,hz,?_,c_empty _ H' (tape_free hr)⟩
  rw [← he]; change ruling A (moment (house H) i)=_; rw [← connected (house H) hA I hI]; exact tutor _ constantCoeff_X (tape_free hr)
end YM.WilsonBulk.Sheet
