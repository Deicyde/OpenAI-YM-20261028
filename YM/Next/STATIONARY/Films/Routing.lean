import YM.Next.STATIONARY.Shape.Shim

set_option autoImplicit false
/-!
# Reading arbitrary probes from local harmonic projections of Hessians.
Actual maps via mixed derivatives, identities pointwise over all waves, not
relying on spectrum interpolation.
-/
noncomputable section
namespace YM.Stationary
open Function Filter Lattice RG Audience Exterior Precision Bloch Wilson Laurent Matrix Finset
open scoped Topology ContDiff BigOperators
variable {α β γ δ ι : Type} {n m k : ℕ}
section probe
variable {X Y Z : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z]
lemma prodT (v : Fin n→X) (p : X) (F : X→Y) (x : X) (hf : ContDiffAt ℝ ω F x) :
    iteratedFDeriv ℝ n (fun t => fderiv ℝ F t p) x v=iteratedFDeriv ℝ (n+1) F x (Fin.snoc v p) := by
  let T := fderiv ℝ F
  let L := ContinuousLinearMap.apply ℝ Y p
  rw [iteratedFDeriv_succ_apply_right]
  rw [Fin.init_snoc, Fin.snoc_last]; exact DFunLike.congr_fun (L.iteratedFDeriv_comp_left (hf.fderiv_right (by simp : ω+1≤(ω:WithTop ℕ∞))) le_top) v
lemma prodW (v : Fin n→X) (p q : X) (F : X→Y) (x : X) (hf : ContDiffAt ℝ ω F x) :
    iteratedFDeriv ℝ n (fun t => iteratedFDeriv ℝ 2 F t ![p,q]) x v=iteratedFDeriv ℝ (n+2) F x (Fin.snoc (Fin.snoc v p) q) := by
  have hz : (fun t => iteratedFDeriv ℝ 2 F t ![p,q]) = fun t => (fderiv ℝ (fderiv ℝ F) t p q) := funext (fun t => iteratedFDeriv_two_apply ..)
  rw [hz,iteratedFDeriv_succ_apply_right]
  have hh : ContDiffAt ℝ ω (fderiv ℝ F) x := hf.fderiv_right (by simp)
  rw [Fin.init_snoc,Fin.snoc_last, ← prodT (F:=fderiv ℝ F) v p _ hh]
  let T := ContinuousLinearMap.apply ℝ Y q
  exact DFunLike.congr_fun (T.iteratedFDeriv_comp_left ((hh.fderiv_right (by simp : ω+1≤(ω:WithTop ℕ∞))).clm_apply (g:=fun _ => p) contDiffAt_const) le_top) v

lemma saves_p (L : X →L[ℝ] Y) (K : Z→L[ℝ] Y) {F : Y→ℝ} (h : ContDiffAt ℝ ω F 0) : ∀ᶠ i : X in 𝓝 0, fderiv ℝ (fun v => F (L i + K v)) 0=fderiv ℝ F (L i) ∘L K := by
  filter_upwards [(show Tendsto L _ (𝓝 0) from by simpa using L.continuous.tendsto 0).eventually (h.eventually (by simp))] with i hi
  exact ((show HasFDerivAt F (fderiv ℝ F (L i)) (L i+K 0) by rw [map_zero,add_zero]; exact (hi.differentiableAt (by simp)).hasFDerivAt).comp 0 (K.hasFDerivAt.const_add (L i))).fderiv
lemma saves_v (L : X→L[ℝ] Y) (K : Z→L[ℝ] Y) {F : Y→ℝ} (h : ContDiffAt ℝ ω F 0) : ∀ᶠ i : X in 𝓝 0, ∀ n : ℕ, ∀ p : Fin n → Z, iteratedFDeriv ℝ n (fun v => F (L i + K v)) 0 p=iteratedFDeriv ℝ n F (L i) (K∘p) := by
  filter_upwards [(show Tendsto L _ (𝓝 0) from by simpa using L.continuous.tendsto 0).eventually (h.eventually (by simp))] with i hi n p
  let V := fun v => F (L i+v)
  have he : AnalyticAt ℝ V 0 := ((show ContDiffAt ℝ ω F (L i+0) by rw [add_zero]; exact hi).comp (0:Y) (contDiffAt_const.add contDiffAt_id)).analyticAt
  change iteratedFDeriv ℝ n (V∘K) 0 p= _
  rw [wired K (by rw [map_zero]; exact he),map_zero]; unfold V; rw [iteratedFDeriv_comp_add_left,add_zero]
end probe
end YM.Stationary
end

/-! # Extend a real matrix-charge relation. -/
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.Stationary
open Function Filter Lattice RG Audience Exterior Precision Bloch Wilson Laurent Matrix Finset
open scoped Topology ContDiff BigOperators
variable {α β γ δ ι : Type} {n m k : ℕ}
lemma roll_snoc {f : α→β} {p : Fin n→α} {q : α} : Fin.snoc (f∘p) (f q)=f ∘ (Fin.snoc p q) := by ext1 i; cases i using Fin.lastCases <;> simp
lemma snock (p : Fin n→α) (x : α) (i : Fin n) (v : α) : Fin.snoc (update p i v) x=update (Fin.snoc p x : Fin (n+1) → α) i.castSucc v := by
  ext1 j; cases j using Fin.lastCases with
  | last => rw [update_of_ne (Ne.symm (Fin.castSucc_ne_last _))]; simp
  | cast j => by_cases h : i=j; · subst j; simp
              simp [Ne.symm h]
lemma sonnet (p : Fin n→α) (x y : α) : Fin.snoc p y=update (Fin.snoc p x : Fin (n+1)→ α) (Fin.last n) y := by
  ext1 j; cases j using Fin.lastCases with
  | last => simp
  | cast j => rw [update_of_ne (Fin.castSucc_ne_last _)]; simp

section line
variable [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    {V : Type} [Add V] [SMul ℂ V]
lemma chordal {F M : (Fin n → Phase α) → V} (h : ∀ v i, Leads fun p => F (update v i p)) (he : ∀ v i, Leads fun p => M (update v i p)) (hv : ∀ u : Fin n→ Corn α,F (axes∘u)=M (axes∘u)) (x) : F x=M x := by
  classical
  suffices hx : ∀ s : Finset (Fin n), ∀ v : Fin n → Phase α,(∀ i∉s,star (v i)=v i) → F v=M v from hx univ x (by simp)
  intro s; induction s using Finset.induction with
  | empty =>
    intro v hV; let u i := fun j => (v i j).re
    rw [show v=axes∘u from funext fun i => (axes_of_real (hV i (notMem_empty _))).symm]; exact hv u
  | insert a s hp ih =>
    intro v hV; have hc f : F (update v a (axes f))=M (update v a (axes f)) := ih _ fun i hh => by
      by_cases H : i=a
      · subst i; simp
      simp only [H,ne_eq,not_false_eq_true,update_of_ne]; exact hV i (by simp [H,hh])
    simpa only [update_eq_self] using (h v a).buys (he v a) hc (v a)


lemma linear_u (M : RecordM ℂ (Fin n) α) (x : Fin n → Phase α) (i : Fin n) (L : Phase β→ₗ[ℂ] Phase α) : Leads (fun z => M (update x i (L z))) := by
  intro u v; dsimp only; rw [map_add, map_smul,M.map_update_add,M.map_update_smul]
lemma update_arc (T : Phase α→ₗ[ℂ] Phase β) (u : Fin n→ Phase α) (i : Fin n) (p : Phase α) : (⇑T) ∘ update u i p = update (T ∘ u) i (T p) := by funext j; by_cases h : j=i <;> simp [*]
lemma arc_axes (T : Phase α→ₗ[ℂ] Phase β) (L : Corn α →L[ℝ] Corn β) (h : ∀ u,T (axes u)=axes (L u)) (x : Fin n→Corn α) : T ∘ (axes ∘ x)=axes ∘ (L ∘ x) := funext fun i => h _
end line
section rows
variable [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype γ] [DecidableEq γ] [Fintype δ] [DecidableEq δ]
    {M : Corn α → Matrix γ β ℝ}
lemma art_col (h : Memo M 0) (v : Corn β) (i : γ) (p : Fin n→ Corn α) :
    (art M n (axes∘p)*ᵥ axes v) i = ((iteratedFDeriv ℝ n (fun z => (M z*ᵥ v) i) 0 p):ℂ) := by
  let F := fun z => ∑ j : β, v j • M z i j
  have hp : (fun z => (M z*ᵥ v) i)=F := by unfold Matrix.mulVec dotProduct; simp only [F,smul_eq_mul]; congr 1; ext1 z; refine sum_congr rfl fun _ _ => mul_comm ..
  rw [hp]; unfold F art Matrix.mulVec dotProduct; rw [iteratedFDeriv_fun_sum_apply (f:=fun j z => v j • M z i j) (fun j _ => ((h i j).of_le le_top).const_smul _), _root_.sum_apply,Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun j _ => ?_; simp only [Matrix.of_apply]; rw [beat_real,iteratedFDeriv_const_smul_apply' ((h _ _).of_le le_top), _root_.smul_apply]; simp [axes,mul_comm]
lemma art_dot {M : Corn α→ Matrix β β ℝ} (h : Memo M 0) (u v : Corn β) (p : Fin n→Corn α) :
    dotProduct (axes u) (art M n (axes∘p)*ᵥ axes v)= ((iteratedFDeriv ℝ n (fun z => dotProduct u (M z*ᵥ v)) 0 p):ℂ) := by
  have hk i : ContDiffAt ℝ ω (fun z => (M z*ᵥ v) i) 0 := ContDiffAt.sum fun j _ => (h i j).mul contDiffAt_const
  unfold dotProduct; simp_rw [art_col h]; change _= ((iteratedFDeriv ℝ n (fun z => ∑ i, u i • (M z*ᵥ v) i) 0 p : ℝ):ℂ); rw [iteratedFDeriv_fun_sum_apply (f:=fun i z => u i • (M z*ᵥ v) i) (fun i _ => ((hk _).of_le le_top).const_smul _), _root_.sum_apply, Complex.ofReal_sum]
  apply sum_congr rfl; intro i _; rw [iteratedFDeriv_const_smul_apply' ((hk i).of_le le_top),_root_.smul_apply]; simp [axes]

lemma allLeagues (M : Corn α→Matrix γ β ℝ) (v : Fin n→ Phase α) (i : Fin n) : Leads (fun u => art M n (update v i u)) := fun p q => by ext j k; exact Leads.pulse (beat (fun x => M x j k) 0 n) v i p q

variable (L : Corn α →L[ℝ] Corn δ) (K : Corn β →L[ℝ] Corn δ) {S : Phase α →ₗ[ℂ] Phase δ} {T : Phase β →ₗ[ℂ] Phase δ}
    (hs : ∀ u,S (axes u)=axes (L u)) (ht : ∀ u,T (axes u)=axes (K u)) (p : Fin n→Phase α)
include hs ht
lemma allcasts {F : Corn δ →ℝ} (i : γ) (h : Memo M 0) (hc : ContDiffAt ℝ ω F 0) (hp : ∀ᶠ x in 𝓝 0, ∀ y,(M x*ᵥ y) i=fderiv ℝ (fun y => F (L x+K y)) 0 y) (v : Phase β) :
    (art M n p *ᵥ v) i=beat F 0 (n+1) (Fin.snoc (S∘p) (T v)) := by
  refine Leads.buys (p:=fun v => (art M n p*ᵥ v) i) (fun x y => ?_) (q:=fun v => beat F 0 (n+1) (Fin.snoc (S ∘ p) (T v))) ?_ ?_ v
  · exact congr_fun ((Matrix.mulVec_add (art M n p) (axes x) (Complex.I • axes y)).trans (by rw [Matrix.mulVec_smul])) i
  · convert linear_u (beat F 0 _) (Fin.snoc (S∘p) 0) (Fin.last n) T using 1
    ext1 w; rw [← sonnet]
  intro v
  refine chordal (F:=fun p => (art M n p *ᵥ axes v) i) (M:=fun p => beat F 0 (n+1) (Fin.snoc (S∘p) (T (axes v)))) (fun p j a b => congr_fun (?_ : art M n (update p j (axes a+Complex.I • axes b))*ᵥ axes v=art M n (update p j (axes a))*ᵥ axes v+Complex.I • ((art M n (update p j (axes b))) *ᵥ (axes v))) i) (fun p j => ?_) ?_ p
  · have hz := allLeagues M p j a b; dsimp only at hz; rw [hz, Matrix.add_mulVec,Matrix.smul_mulVec]
  · simp_rw [update_arc,snock]; exact linear_u _ _ _ _
  intro u
  rw [art_col h,arc_axes S L hs u,ht,roll_snoc,beat_real]; apply congr_arg (fun x : ℝ => (x : ℂ))
  let V x := fderiv ℝ F x (K v)
  have hF : ContDiffAt ℝ ω V 0 := (hc.fderiv_right (m:=ω) (by simp)).clm_apply (g:=fun _ => K v) contDiffAt_const
  have he : (fun x => (M x*ᵥ v) i) =ᶠ[𝓝 0] (V ∘ L) := by filter_upwards [hp,saves_p L K hc] with x hx hy; rw [hx,hy]; rfl
  rw [(he.iteratedFDeriv ℝ n).eq_of_nhds, wired L (by rw [map_zero]; exact hF.analyticAt),map_zero]; exact prodT _ _ _ _ hc
end rows
end YM.Stationary
end

/-!
# Scalar Hessian chemistry. Includes sealing financed by real identity.
No claims about function off the stencil chart.
-/
noncomputable section
namespace YM.Stationary
open Function Filter Lattice RG Audience Exterior Precision Bloch Wilson Laurent Matrix Finset
open scoped Topology ContDiff BigOperators
variable {α β γ δ ι : Type} {n m : ℕ}
variable [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype γ] [DecidableEq γ] [Fintype δ] [DecidableEq δ]
    {M : Corn α → Matrix β β ℝ}
variable (L : Corn α →L[ℝ] Corn δ) (K : Corn β →L[ℝ] Corn δ) {S : Phase α →ₗ[ℂ] Phase δ} {T : Phase β →ₗ[ℂ] Phase δ}
    (hs : ∀ u,S (axes u)=axes (L u)) (ht : ∀ u,T (axes u)=axes (K u)) (p : Fin n→Phase α)
section broadcast
include hs ht
lemma all_hess {F : Corn δ →ℝ} (h : Memo M 0) (hc : ContDiffAt ℝ ω F 0)
    (hp : ∀ᶠ x in 𝓝 0, ∀ y z,dotProduct y (M x *ᵥ z) = iteratedFDeriv ℝ 2 (fun y => F (L x+K y)) 0 ![y,z]) (u v : Phase β) :
    dotProduct u (art M n p*ᵥ v)=beat F 0 (n+2) (Fin.snoc (Fin.snoc (S∘p) (T u) : Fin (n+1) → Phase δ) (T v)) := by
  let a := art M n p
  refine Leads.two (p:=fun u v => dotProduct u (a*ᵥ v)) (q:=fun u v => beat F 0 (n+2) (Fin.snoc (Fin.snoc (S∘p) (T u) : Fin (n+1) → _) (T v))) (fun v x y => ?_) (fun u x y => ?_) ?_ ?_ ?_ u v
  · simp only [add_dotProduct, smul_dotProduct]
  · simp only [Matrix.mulVec_add, Matrix.mulVec_smul,dotProduct_add,dotProduct_smul]
  · intro v; convert linear_u (beat F 0 _) (Fin.snoc (Fin.snoc (S∘p) 0 : Fin (n+1) → _) (T v)) ((Fin.last n).castSucc) T using 1
    ext1 w; rw [← snock,← sonnet]
  · intro u; convert linear_u (beat F 0 _) (Fin.snoc (Fin.snoc (S∘p) (T u) : Fin (n+1) → _) 0) (Fin.last (n+1)) T using 1
    ext1 w; rw [← sonnet]
  intro w z
  refine chordal (F:=fun p => dotProduct (axes w) (art M n p*ᵥ axes z)) (M:=fun p => beat F 0 (n+2) (Fin.snoc (Fin.snoc (S∘p) (T (axes w)) : Fin (n+1) → _) (T (axes z)))) (fun p j x y => ?_) (fun p j => ?_) ?_ p
  · have he := allLeagues M p j x y; dsimp only at he; simp only [he,Matrix.add_mulVec,Matrix.smul_mulVec,dotProduct_add,dotProduct_smul]
  · simp_rw [update_arc,snock]; exact linear_u _ _ _ _
  intro p
  rw [art_dot h, arc_axes S L hs,ht,ht,roll_snoc,roll_snoc,beat_real]; apply congr_arg (fun x : ℝ => (x : ℂ))
  let V x := iteratedFDeriv ℝ 2 F x ![K w,K z]
  have hV : ContDiffAt ℝ ω V 0 := by
    unfold V; simp_rw [iteratedFDeriv_two_apply]; apply ContDiffAt.clm_apply (g:=fun _ => K z) _ contDiffAt_const; exact (((hc.fderiv_right (m:=ω) (by simp)).fderiv_right (m:=ω) (by simp)).clm_apply (g:=fun _ => K w) contDiffAt_const)
  have he : (fun x => dotProduct w (M x*ᵥ z)) =ᶠ[𝓝 0] (V ∘ L) := by
    filter_upwards [hp,saves_v L K hc] with x hx hy; rw [hx,hy, show K ∘ ![w,z]= ![K w,K z] by ext1 j; fin_cases j <;> rfl]; rfl
  rw [(he.iteratedFDeriv ℝ n).eq_of_nhds, wired L (by rw [map_zero]; exact hV.analyticAt),map_zero]; exact prodW _ _ _ _ _ hc
end broadcast

section seals
lemma cast_memo {M : Corn α → Matrix γ β ℝ} {F : γ→Corn δ →ℝ} (h : ∀ i, ContDiffAt ℝ ω (F i) 0) (hp : ∀ i,∀ᶠ x in 𝓝 0,∀ y,(M x*ᵥ y) i=fderiv ℝ (fun y => F i (L x+K y)) 0 y) : Memo M 0 := by
  intro i j; let v : Corn β := Pi.single j 1
  let V := fun x => fderiv ℝ (F i) x (K v)
  apply ContDiffAt.congr_of_eventuallyEq (f:=V ∘ L)
  · refine ContDiffAt.comp _ ?_ L.contDiff.contDiffAt
    rw [map_zero]; exact ((h i).fderiv_right (m:=ω) (by simp)).clm_apply (g:=fun _ => K v) contDiffAt_const
  filter_upwards [hp i, saves_p L K (h i)] with x hx hy
  rw [show M x i j=(M x*ᵥ v) i by simp [v,Matrix.mulVec_single],hx,hy]; rfl
lemma play_memo {F : Corn δ →ℝ} (h : ContDiffAt ℝ ω F 0) (hp : ∀ᶠ x in 𝓝 0,∀ y z,dotProduct y (M x*ᵥ z)=iteratedFDeriv ℝ 2 (fun y => F (L x+K y)) 0 ![y,z]) : Memo M 0 := by
  intro i j; let w : Corn β := Pi.single i 1; let z : Corn β := Pi.single j 1
  let V := fun x => iteratedFDeriv ℝ 2 F x ![K w,K z]; apply ContDiffAt.congr_of_eventuallyEq (f:=V ∘ L)
  · refine ContDiffAt.comp _ ?_ L.contDiff.contDiffAt; rw [map_zero]; unfold V; simp_rw [iteratedFDeriv_two_apply]; apply ContDiffAt.clm_apply (g:=fun _ => K z) _ contDiffAt_const; exact (((h.fderiv_right (m:=ω) (by simp)).fderiv_right (m:=ω) (by simp)).clm_apply (g:=fun _ => K w) contDiffAt_const)
  filter_upwards [hp,saves_v L K h] with x hx hy
  rw [show M x i j=dotProduct w (M x*ᵥ z) by simp [w,z,Matrix.mulVec_single],hx,hy, show K ∘ ![w,z]=![K w,K z] by ext1 i; fin_cases i <;> rfl]; rfl
end seals
end YM.Stationary
end

/-!
# Cinema ticket conversion from n-cast
-/
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.Stationary
open Function Filter Lattice RG Audience Exterior Precision Bloch Wilson Laurent Matrix Finset
open scoped Topology ContDiff BigOperators
variable {α β γ δ ι : Type} {c f : Side} {G : Gauge} {P : Patch} {K : KernelChoices} {C D σ : ℝ} {m n : ℕ} {p : Momentum}
variable [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype γ] [DecidableEq γ] [Fintype ι] [DecidableEq ι]

-- mapping potential eye-injections, Θ exact.
abbrev Eye (A B : Type) := Momentum → Phase A→ₗ[ℂ] Phase B
structure Turns (p : Eye α β) (L : Corn (Co c α)→L[ℝ] Corn (Co c β)) : Prop where
  basis : ∃ T : Phase (Co c α) →ₗ[ℂ] Phase (Co c β), (∀ u, T (axes u)=axes (L u)) ∧ ∀ i : Site c,∀ q,rolls (mon i) q → ∀ v,T (tune i v)=tune i (p q v)

abbrev Leagues (ι α β : Type) := (n : ℕ) → (Fin n → Momentum) → (Fin n → ι) → Momentum → CompM α β
def recitalX (K : Leagues ι α β) : Film ι α β := ⟨K 0 ![] ![],fun i p => K 1 ![p] ![i],fun i j p q => K 2 ![p,q] ![i,j]⟩
lemma art_zero (M : Corn α → Matrix β γ ℝ) : art M 0 ![] = cardM M := by
  ext i j; unfold art; rw [Matrix.of_apply,show (![] : Fin 0→Phase α)=axes ∘ (![] : Fin 0 → Corn α) from Subsingleton.elim ..,beat_real,iteratedFDeriv_zero_apply]; rfl
lemma all_ground {K : Leagues ι α β} {M : OperatorF ι c α β} (h : Memo M 0) (hp : ∀ n (p : Fin n → Momentum) (i : Fin n→ι) (v : Fin n→ Site c), (∀ j, rolls (mon (v j)) (p j)) → Jaunt (art M n (fun j => relay (v j) (i j))) (K n p i) (∑ j,v j)) : Ticket (recitalX K) M := by
  refine ⟨h,?_,fun i p q he => ?_, fun i j p q a b he hx => ?_⟩
  · rw [← art_zero]
    have hx := hp 0 ![] ![] ![] (by rintro ⟨k,h⟩; omega); simpa only [show (fun j => relay (m:=c) ((![]:Fin 0→_) j) ((![]:Fin 0→ι) j))=![] from Subsingleton.elim ..,sum_empty,Finset.univ_eq_empty,recitalX] using hx
  · unfold seat; change Jaunt _ (K 1 ![q] ![i]) p
    have ht := hp 1 ![q] ![i] ![p] (fun j => by fin_cases j; exact he)
    rw [show (fun j => relay ((![p]:Fin 1 → _) j) ((![i]:Fin 1 → _) j))= ![relay p i] by ext1 k; fin_cases k; rfl,Fin.sum_univ_one] at ht; exact ht
  unfold cart; change Jaunt _ (K 2 ![a,b] ![i,j]) _
  have ht := hp 2 ![a,b] ![i,j] ![p,q] (fun k => by fin_cases k; exact he; exact hx)
  rw [show (fun k => relay ((![p,q]:Fin 2→_) k) ((![i,j]:Fin 2→_) k))=![relay p i,relay q j] by ext1 k; fin_cases k <;> rfl,Fin.sum_univ_two] at ht; exact ht

-- author of recall: joint functions, toll κ

def sunshift (p : Fin n→ Momentum) (q : Momentum) := q+∑ i,p i
def inviton (A : Eye ι (Acts G P)) (b : Fin n→ ι) (p : Fin n→ Momentum) (i : Fin n) := A (p i) (Pi.single (b i) 1)
def lens (x : Fin n→Phase (Acts G P)) (q : Fin n→Momentum) (i : Fin n) := imprintsC G P (q i) (x i)

-- Coulomb ext variables left first followed by all inserted T-legs in scalar derivatives, last is incoming.
def mentor (M : α→ BassInput G P →ℝ) (B : Eye ι (Acts G P)) (K : Eye β (Acts G P)) : Leagues ι α β := fun n p i q => Matrix.of fun b j =>
    beat (M b) 0 (n+1) (Fin.snoc (lens (inviton B i p) p) (imprintsC G P q (K q (Pi.single j 1))))
def sailor (M : BassInput G P →ℝ) (B : Eye ι (Acts G P)) (K : Eye β (Acts G P)) : Leagues ι β β := fun n p i q => Matrix.of fun b j =>
    let t := - sunshift p q
    beat M 0 (n+2) (Fin.snoc (Fin.snoc (lens (inviton B i p) p) (imprintsC G P t (K t (Pi.single b 1))) : Fin (n+1) → _) (imprintsC G P q (K q (Pi.single j 1))))

lemma by_bills (K : Phase β→ₗ[ℂ] Phase (Piano G P)) (j : Fin n) (x : Fin n→ Phase (Piano G P)) (Q : RecordM ℂ (Fin n) (Piano G P)) (z : Phase β) :
    Q (update x j (K z))=∑ i,Q (update x j (K (Pi.single i 1)))*z i := by
  let L : Phase β →ₗ[ℂ] ℂ := (Q.toLinearMap x j).comp K
  change L z=∑ i,L _ *z i
  conv_lhs => rw [show z=∑ i,z i • Pi.single i (1:ℂ) by
    ext1 i; simp [Finset.sum_apply,Pi.single_apply]]
  rw [map_sum]; apply Finset.sum_congr rfl; intro i _; rw [map_smul]; exact mul_comm ..
lemma shore_snoc (K : Phase β→ₗ[ℂ] Phase (Piano G P)) (x : Fin n→ Phase (Piano G P)) (M : BassInput G P →ℝ) (z : Phase β) : beat M 0 (n+1) (Fin.snoc x (K z)) = ∑ i, beat M 0 (n+1) (Fin.snoc x (K (Pi.single i 1)))*z i := by
  have ht := by_bills K (Fin.last n) (Fin.snoc x 0) (beat M 0 _) z; simp_rw [← sonnet] at ht; exact ht

variable {B : Eye ι (Acts G P)} {T : Eye β (Acts G P)} {x : Fin n→Momentum} {b : Fin n→ι}
lemma mentors (M : α → BassInput G P →ℝ) (u : Phase β) (i) :
    (mentor M B T n x b p *ᵥ u) i=beat (M i) 0 (n+1) (Fin.snoc (lens (inviton B b x) x) (imprintsC G P p (T p u))) := Eq.symm (shore_snoc ((imprintsC G P p).comp (T p)) _ _ u)
lemma sailing (M : BassInput G P →ℝ) (u v : Phase β) (t : Momentum) (h : t= -sunshift x p) :
    dotProduct u (sailor M B T n x b p *ᵥ v)= beat M 0 (n+2) (Fin.snoc (Fin.snoc (lens (inviton B b x) x) (imprintsC G P t (T t u)) : Fin (n+1) → _) (imprintsC G P p (T p v))) := by
  let S := sailor M B T n x b p
  let X := lens (inviton B b x) x
  let K := (imprintsC G P t).comp (T t)
  let Q := (imprintsC G P p).comp (T p)
  let Z (z : Phase β) : Fin (n+1) → _ := Fin.snoc X (K z)
  have he i : (S*ᵥ v) i=beat M 0 _ (Fin.snoc (Z (Pi.single i 1)) (Q v) : Fin (n+2)→_) := by rw [shore_snoc Q]; subst t; rfl
  have hv := by_bills K (Fin.castSucc (Fin.last n)) (Fin.snoc (Fin.snoc X 0 : Fin (n+1) → _) (Q v)) (beat M 0 (n+2)) u; simp_rw [← snock,← sonnet] at hv
  change (∑ i,u i*(S*ᵥ v) i)=_
  refine Eq.trans ?_ hv.symm; simp_rw [he]; exact Finset.sum_congr rfl fun _ _ => mul_comm ..
end YM.Stationary
end

/-! # Local receipts to whole period. Existence comparison is with Hess or
row maps, not copied approximants. -/
noncomputable section
namespace YM.Stationary
open Function Filter Lattice RG Audience Exterior Precision Bloch Wilson Laurent Matrix Finset
open scoped Topology ContDiff BigOperators
variable {α β γ δ ι : Type} {c f : Side} {G : Gauge} {P : Patch} {K : KernelChoices} {C D σ : ℝ} {m n : ℕ} {p : Momentum}

lemma snocked {ι β δ : Type} (F : ι → β → δ) (v : Fin n → ι) (b : Fin n→ β) (x y) : (fun i : Fin (n+1) => F ((Fin.snoc v x : Fin (n+1)→ ι) i) ((Fin.snoc b y : Fin (n+1)→ β) i))=Fin.snoc (fun i => F (v i) (b i)) (F x y) := by ext1 i; cases i using Fin.lastCases <;> simp
lemma snockedR {ι β : Type} (F : ι→β→Prop) (v : Fin n→ι) (b : Fin n→β) (h : ∀ i,F (v i) (b i)) {x y} (p : F x y) (i : Fin (n+1)) : F ((Fin.snoc v x : Fin (n+1)→ ι) i) ((Fin.snoc b y : Fin (n+1)→ β) i) := by
  rw [show F _ _= _ from congr_fun (snocked F v b x y) i]; cases i using Fin.lastCases <;> simp [p,h]
lemma snocked_sum {α : Type} [AddCommMonoid α] (v : Fin n→α) (u : α) : (∑ i, (Fin.snoc v u : Fin (n+1) → _) i)=(∑ i,v i)+u := by rw [Fin.sum_univ_castSucc]; simp
lemma beat_summations [Fintype α] [DecidableEq α] (s : Finset δ) (F : δ → Corn α→ℝ) (h : ∀ i∈s,ContDiffAt ℝ ω (F i) 0) (v : Fin n → Phase α) : beat (fun x => ∑ i∈s,F i x) 0 n v= ∑ i∈s,beat (F i) 0 n v := by
  refine chordal (F:=fun v => _) (M:=fun v => ∑ i∈s,beat (F i) 0 n v) (Leads.pulse _) (fun p j x y => ?_) ?_ v
  · have hx i : beat (F i) 0 n (update p j (axes x+Complex.I • axes y))=_ := (beat (F i) 0 n).map_update_add ..
    simp only [hx,MultilinearMap.map_update_smul,sum_add_distrib,Finset.smul_sum]
  intro u
  simp only [beat_real]; rw [iteratedFDeriv_fun_sum_apply (fun i hi => (h i hi).of_le le_top),_root_.sum_apply,Complex.ofReal_sum]

variable [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype γ] [DecidableEq γ] [Fintype ι] [DecidableEq ι]
    (S : StepData c f)
variable (L : Corn (Co c ι)→L[ℝ] Corn (Co c (Acts G S.patch))) (K : Corn (Co c β) →L[ℝ] Corn (Co c (Acts G S.patch)))
    {B : Eye ι (Acts G S.patch)} {T : Eye β (Acts G S.patch)}

-- potential one-site outputs. L,K globally linear; real tests group-connected.
abbrev muralMap (S : StepData c f) (F : BassInput G S.patch→ℝ) : Corn (Co c (Acts G S.patch)) → ℝ := fun z => ∑ i,F (rehearsal S i z)

theorem mentoring {M : OperatorF ι c α β} (h : Turns B L) (p : Turns T K) (F : α → BassInput G S.patch→ℝ) (hc : ∀ i,ContDiffAt ℝ ω (F i) 0) (hp : ∀ (i : Co c α),∀ᶠ x in 𝓝 0,∀ y,(M x*ᵥ y) i=fderiv ℝ (fun z => F i.2 (rehearsal S i.1 (L x + K z))) 0 y) : Ticket (recitalX (mentor F B T)) M := by
  classical
  let X := fun i : Co c α => F i.2∘rehearsal S i.1
  have hX i : ContDiffAt ℝ ω (X i) 0 := (show ContDiffAt ℝ ω (F i.2) (rehearsal S i.1 (0:_)) by rw [map_zero]; exact hc _).comp _ (rehearsal (G:=G) S i.1).contDiff.contDiffAt
  have hx : Memo M 0 := cast_memo L K (F:=X) hX hp
  refine all_ground hx fun n P b a hz q z he v => ?_
  obtain ⟨U,hU,hu⟩ := h.basis
  obtain ⟨V,hV,hv⟩ := p.basis
  let A := fun i => relay (a i) (b i)
  let R := inviton B b P
  have ht : U∘A=fun i => tune (a i) (R i) := funext fun i => hu _ _ (hz i) (Pi.single (b i) 1)
  let Mq : Fin (n+1) → Momentum := Fin.snoc P z
  let Tq : Fin (n+1) → Site c := Fin.snoc a q
  let Wq : Fin (n+1) → Phase (Acts G S.patch) := Fin.snoc R (T z v)
  ext1 i
  rw [show (art M n A *ᵥ tune q v) i=_ from allcasts L K hU hV A i hx (hX i) (hp i) _]
  have hy := audition S Tq Mq (snockedR (fun i z => rolls (mon i) z) a P hz he) Wq i.1 (F i.2) (hc _ |>.analyticAt)
  rw [ht,hv q z he v, ← show (fun i : Fin (n+1) => tune (Tq i) (Wq i))= _ from (snocked (fun i x => tune i x) a R q (T z v)), show X i=_ from rfl]
  rw [hy]
  change cell _ _*_=cell _ _*((mentor F B T n P b z *ᵥ v) i.2)
  rw [snocked_sum a q,add_comm (∑ j,a j),mentors]; congr 2
  exact snocked (fun i x => imprintsC G S.patch i x) P R z (T z v)

theorem mariner {M : OperatorF ι c β β} (h : Turns B L) (p : Turns T K) (F : BassInput G S.patch→ℝ) (hc : ContDiffAt ℝ ω F 0) (hp : ∀ᶠ x in 𝓝 0,∀ y z,dotProduct y (M x*ᵥ z)=iteratedFDeriv ℝ 2 (fun v => ∑ i,F (rehearsal S i (L x + K v))) 0 ![y,z]) : Ticket (recitalX (sailor F B T)) M := by
  classical
  let X := muralMap S F
  have he i : ContDiffAt ℝ ω (F ∘ rehearsal S i) 0 := (show ContDiffAt ℝ ω F (rehearsal S i (0:_)) by rw [map_zero]; exact hc).comp _ (rehearsal (G:=G) S i).contDiff.contDiffAt
  have hX : ContDiffAt ℝ ω X 0 := ContDiffAt.sum fun i _ => he i
  have hx : Memo M 0 := play_memo L K hX hp
  obtain ⟨U,hU,hu⟩ := h.basis
  obtain ⟨V,hV,hv⟩ := p.basis
  refine all_ground hx fun n P b a hz q z heq v => ray_book _ _ (fun t w => ?_)
  let A := fun i => relay (a i) (b i)
  let R := inviton B b P; let i := -sunshift P z
  have ht : U∘A=fun i => tune (a i) (R i) := funext fun i => hu _ _ (hz i) (Pi.single (b i) 1)
  let d := t+(q+∑ j,a j)
  have hd y (h : rolls (mon t) y) : dotProduct (tune t w) (art M n A*ᵥ tune q v)=
      (∑ j : Site c,cell d j)* beat F 0 (n+2) (Fin.snoc (Fin.snoc (lens R P) (imprintsC G S.patch y (T y w)) : Fin (n+1)→_) (imprintsC G S.patch z (T z v))) := by
    rw [show dotProduct _ _=(beat X 0 (n+2) _) from all_hess L K hU hV A hx hX hp (tune t w) _, ht,hv t y h w,hv q z heq v]
    let W : Fin (n+2)→ Site c := Fin.snoc (Fin.snoc a t : Fin (n+1) → _) q
    let Y : Fin (n+2)→ Momentum := Fin.snoc (Fin.snoc P y : Fin (n+1) → _) z
    let J : Fin (n+2)→ Phase (Acts G S.patch) := Fin.snoc (Fin.snoc R (T y w) : Fin (n+1) → _) (T z v)
    rw [← snocked (fun i x => tune i x) a R t (T y w), ← snocked (fun i x => tune i x) (Fin.snoc a t) (Fin.snoc R (T y w)) q (T z v),show X=(fun z => ∑ i,(F ∘ rehearsal S i) z) from rfl, beat_summations (α:=Co c (Acts G S.patch)) univ (fun i => F ∘ rehearsal S i) (fun i _ => he i), Finset.sum_mul]
    refine sum_congr rfl fun j _ => ?_
    rw [show beat (F ∘ rehearsal S j) 0 (n+2) _ = _ from audition S W Y (snockedR (fun i z => rolls (mon i) z) (Fin.snoc a t) (Fin.snoc P y) (snockedR (fun i z => rolls (mon i) z) a P hz h) heq) J j F hc.analyticAt]
    have hz : ∑ i,W i=d := by unfold W d; rw [snocked_sum,snocked_sum]; abel
    rw [hz]; apply congr_arg (cell d j*·); apply congr_arg
    unfold J Y; rw [snocked (fun i x => imprintsC G S.patch i x) _ _ z (T z v),snocked (fun i x => imprintsC G S.patch i x) P R]
    rfl
  rw [ray_dots]; split
  next hp =>
    have hE := ht; clear hE
    have hz := hd i (by rw [eq_neg_of_add_eq_zero_left hp]; exact (heq.combine (collide a P hz)).flip_sign)
    rw [show d=0 from hp] at hz; simpa [A,R,cell,sum_const,nsmul_eq_mul, sailing (B:=B) F w v i rfl] using hz
  next hp =>
    have hh := hd (mon t) (rolls.refl _); rw [sum_cell hp,zero_mul] at hh; exact hh
end YM.Stationary
end

/-!
# Noether contours for readings. Differentiability on joint openings.
-/
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.Stationary
open Function Filter Lattice RG Audience Exterior Precision Bloch Wilson Laurent Matrix Finset
open scoped Topology ContDiff BigOperators
variable {α β γ δ ι : Type} {c f : Side} {G : Gauge} {P : Patch} {K : KernelChoices} {C D σ : ℝ} {m n : ℕ} {p q r : Momentum}
-- strip of eye (admits only inside)
structure Fresh [Fintype α] [Fintype β] (E : Eye α β) (σ : ℝ) : Prop where
    shifts {p q : Momentum} (h : rolls p q) : p∈strip σ → E p=E q
    sense {p : Momentum} : p∈strip σ → ∀ i, DifferentiableAt ℂ (fun x => E x i) p
variable [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype γ] [DecidableEq γ] [Fintype ι] [DecidableEq ι]
    {B : Eye ι (Acts G P)} {T : Eye β (Acts G P)} {E : Eye γ β}
lemma rolls_sums {p q : Fin n→Momentum} (h : ∀ i,rolls (p i) (q i)) : rolls (∑ i,p i) (∑ i,q i) := by
  suffices hi : ∀ s : Finset (Fin n),rolls (∑ i∈s,p i) (∑ i∈s,q i) from hi univ
  intro i; induction i using Finset.induction with
  | empty => simp only [sum_empty]; exact rolls.refl _
  | insert j s he ih => rw [sum_insert he, sum_insert he]; exact (h j).plus ih

section analytic
variable {X : Type} [NormedAddCommGroup X] [NormedSpace ℂ X]

lemma differentiableBeat {u : X→ Fin n → Phase α} {x : X} (hp : ∀ i,DifferentiableAt ℂ (fun x => u x i) x) (M : RecordM ℂ (Fin n) α) : DifferentiableAt ℂ (fun z => M (u z)) x := ((listen M).contDiff (n:=ω)).contDiffAt.differentiableAt (by simp) |>.comp x (differentiableAt_pi.mpr hp)
lemma diff_snoc {u : X→ Fin n→ Phase α} {v : X→Phase α} {x : X} (h : ∀ i,DifferentiableAt ℂ (fun x => u x i) x) (hp : DifferentiableAt ℂ v x) (j : Fin (n+1)) : DifferentiableAt ℂ (fun y => (Fin.snoc (u y) (v y) : Fin (n+1) → _) j) x := by
  cases j using Fin.lastCases <;> simp [h,hp]

lemma cosmic (K : Leagues ι α β) (h : ∀ n (p r : Fin n → Momentum) (i : Fin n →ι) q z, (∀ i,rolls (p i) (r i)) → rolls q z → (∀ i,p i∈strip σ) → q∈strip σ → sunshift p q∈strip σ → K n p i q=K n r i z)
    (hp : ∀ (X : Type) [NormedAddCommGroup X] [NormedSpace ℂ X] (x : X) (n : ℕ) (p : X → Fin n→Momentum) (q : X → Momentum) (b : Fin n→ι), (∀ i, p x i∈strip σ) → q x∈strip σ → sunshift (p x) (q x)∈strip σ → (∀ i, DifferentiableAt ℂ (fun z => p z i) x) → DifferentiableAt ℂ q x → BillD (fun z => K n (p z) b (q z)) x) : Play (recitalX K) σ := by
  constructor
  · refine ⟨fun w => hp Momentum _ 0 (fun _ => ![]) id ![] (by simp) w (by simpa [sunshift]) (by simp) differentiableAt_id, fun he w => h 0 _ _ _ _ _ (by simp) he (by simp) w (by simpa [sunshift]) ⟩
  · intro i
    refine ⟨fun w => hp _ _ 1 (fun z : Momentum × Momentum => ![z.1]) Prod.snd ![i] ?_ w.basic ?_ ?_ differentiableAt_snd, fun h1 h2 w => h 1 _ _ _ _ _ ?_ h2 ?_ w.basic ?_⟩
    · intro j; fin_cases j; exact w.side
    · simpa [sunshift] using w.added
    · intro j; fin_cases j; exact differentiableAt_fst
    · intro j; fin_cases j; exact h1
    · intro j; fin_cases j; exact w.side
    simpa [sunshift] using w.added
  intro i j
  refine ⟨fun {p q r} w => hp _ _ 2 (fun z : Momentum×Momentum ×Momentum => ![z.1,z.2.1]) (fun (z : Momentum×Momentum×Momentum) => z.2.2) ![i,j] ?_ w.oneWay.basic ?_ ?_ (by fun_prop), fun h1 h2 h3 w => h 2 _ _ _ _ _ ?_ h3 ?_ w.oneWay.basic ?_⟩
  · intro l; fin_cases l; exact w.oneWay.side; exact w.second.side
  · simpa [sunshift,Fin.sum_univ_two] using w.total
  · intro l; fin_cases l; exact differentiableAt_fst; change DifferentiableAt ℂ (fun z : Momentum×Momentum×Momentum => z.2.1) _; fun_prop
  · intro l; fin_cases l; exact h1; exact h2
  · intro l; fin_cases l; exact w.oneWay.side; exact w.second.side
  simpa [sunshift,Fin.sum_univ_two] using w.total
lemma cosmic_mentor (h : Fresh B σ) (hp : Fresh T σ) (M : γ → BassInput G P →ℝ) : Play (recitalX (mentor M B T)) σ := by
  refine cosmic _ ?_ ?_
  · intro n p r i q z h1 h2 w1 w2 w3; have he : lens (inviton B i p) p=lens (inviton B i r) r := by ext1 k; unfold lens inviton; rw [flips_melody _ (h1 k),h.shifts (h1 k) (w1 k)]
    ext a b; unfold mentor; simp only [Matrix.of_apply]; rw [he,flips_melody _ h2,hp.shifts h2 w2]
  intro X _ _ x n p q b w1 w2 w3 hP hQ i j
  unfold mentor; simp only [Matrix.of_apply]
  apply differentiableBeat _
  apply diff_snoc (u:=fun x => lens (inviton B b (p x)) (p x)) (v:=fun x => imprintsC G P (q x) (T (q x) (Pi.single j 1)))
  · intro i; apply melody_diff; exact (h.sense (w1 i) _).comp (f:=fun y=> p y i) x (hP i); exact hP i
  apply melody_diff; exact (hp.sense w2 _).comp _ hQ; exact hQ

lemma cosmic_sail (h : Fresh B σ) (hp : Fresh T σ) (M : BassInput G P →ℝ) : Play (recitalX (sailor M B T)) σ := by
  refine cosmic _ ?_ ?_
  · intro n p r i q z h1 h2 w1 w2 w3; have he : lens (inviton B i p) p=lens (inviton B i r) r := by ext1 k; unfold lens inviton; rw [flips_melody _ (h1 k),h.shifts (h1 k) (w1 k)]
    have ht : rolls (-sunshift p q) (-sunshift r z) := (h2.plus (rolls_sums h1)).neg
    ext a b; unfold sailor; simp only [Matrix.of_apply]; rw [he,flips_melody _ h2,hp.shifts h2 w2,flips_melody _ ht,hp.shifts ht (negResident w3)]
  intro X _ _ x n p q b w1 w2 w3 hP hQ i j
  unfold sailor; simp only [Matrix.of_apply]
  let v := fun z => -sunshift (p z) (q z)
  have hv : DifferentiableAt ℂ v x := (hQ.add (DifferentiableAt.fun_sum fun k _ => hP k)).neg
  let u := fun z => (Fin.snoc (lens (inviton B b (p z)) (p z)) (imprintsC G P (v z) (T (v z) (Pi.single i 1))) : Fin (n+1) → _)
  apply differentiableBeat _
  apply diff_snoc (u:=u) (v:=fun x => imprintsC G P (q x) (T (q x) (Pi.single j 1)))
  · apply diff_snoc (u:=fun x => lens (inviton B b (p x)) (p x)) (v:=fun x => imprintsC G P (v x) (T (v x) (Pi.single i 1)))
    · intro i; apply melody_diff; exact (h.sense (w1 i) _).comp (f:=fun y=> p y i) x (hP i); exact hP i
    exact melody_diff ((hp.sense (p:=v x) (negResident w3) _).comp x hv) hv
  exact melody_diff ((hp.sense w2 _).comp x hQ) hQ
end analytic
end YM.Stationary
end

/-!
# Wire salient external pencils. No spectrum assumed, not paying arbitrary
frame representatives. `Themes` use L on the portfolio cell, in chart.
-/
noncomputable section
namespace YM.Stationary
open Function Filter Lattice RG Audience Exterior Precision Bloch Wilson Laurent Matrix Finset
open scoped Topology ContDiff BigOperators
variable {α β γ : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] {G : Gauge} {P : Patch} {c f n : Side} {p : Momentum} {σ C : ℝ}

lemma Fresh.placed (F : Phase α →ₗ[ℂ] Phase β) : Fresh (fun _ => F) σ := ⟨fun _ _ => rfl,fun _ _ => differentiableAt_const _⟩
lemma Fresh.enter {Φ : Bridge G P} (h : Poster σ Φ) : Fresh (arriving Φ) σ := by
  refine ⟨fun he w => ?_, fun {p} hP v => ?_⟩
  · apply LinearMap.ext; intro x; simp only [arriving,arranging,LinearMap.coe_mk,AddHom.coe_mk,h.shifts he w]
  apply differentiableAt_pi.mpr; intro i; rcases i with i|((i|i)|i)
  · exact differentiableAt_const _
  · change DifferentiableAt ℂ (fun p => ∑ j : Loc G 1, Φ p i j*v j) p
    exact DifferentiableAt.fun_sum fun j _ => (h.shape hP i j).mul_const _
  · exact differentiableAt_const _
  cases i <;> exact differentiableAt_const _



section arc
variable (S : StepData c f)

-- Inputs supplied by actual producer

def Premise (W : Matrix (Body 1 f) (Body 1 c) ℝ) (Φ : Bridge G S.patch) := Jaunt (approached (repackM (unitSplit G S 1) (Equiv.refl _) (patron G W))) Φ 0

-- Rewired linear pathways to global deck. L binds via Θ at origin. `_term` matrix.
def atlasQ (W : Matrix (Body 1 f) (Body 1 c) ℝ) : Link G c →L[ℝ] Corn (Co c (Acts G S.patch)) :=
    (pavilionB G S).toContinuousLinearMap ∘L (saluteLe (G:=G) W).prod 0
def orbitR (b : Bool) : WarpV G S→L[ℝ] Corn (Co c (Acts G S.patch)) :=
    (pavilionB G S).toContinuousLinearMap ∘L ((show Vault G c f →L[ℝ] Bang G c f from
      if b then (ContinuousLinearMap.inr ..) ∘L ContinuousLinearMap.inl .. else (ContinuousLinearMap.inl ..) ∘L ContinuousLinearMap.inr ..) ∘L (directX G S).symm.toContinuousLinearMap)
def orbitV : Link G c→L[ℝ] Corn (Co c (Acts G S.patch)) := (pavilionB G S).toContinuousLinearMap ∘L ((ContinuousLinearMap.inr ..) ∘L ContinuousLinearMap.inr ..)

def spinGather
    (T : Phase α →ₗ[ℂ] Phase β) : Phase (Co n α)→ₗ[ℂ] Phase (Co n β) := LinearMap.pi (fun i : Co n β => (LinearMap.proj i.2) ∘ₗ T ∘ₗ LinearMap.pi fun j : α => LinearMap.proj (i.1,j))
lemma spinMoves (T : Phase α→ₗ[ℂ] Phase β) (p : Site n) (u : Phase α) : spinGather T (tune p u) = tune p (T u) := by
  ext1 i
  change T (cell p i.1 • u) i.2=_; rw [map_smul]; rfl

lemma orbit_path (b : Bool) : Turns (fun _ => visibly S.patch b) (orbitR (G:=G) S b) := by
  classical
  refine ⟨spinGather (visibly _ b),fun u => ?_,fun p q _ v => spinMoves _ p v⟩
  cases b <;> ext1 i <;> rcases i with ⟨i,j|(j|(j|j))⟩
  · change (0:ℂ)= ↑(0:ℝ); simp
  · change _=((directX G S ((directX G S).symm u) (i,j):ℝ):ℂ); rw [(directX G S).apply_symm_apply]; rfl
  · change (0:ℂ)= ↑(directX G S 0 (i,j)); simp
  · change (0:ℂ)= ↑(0:ℝ); simp
  · change (0:ℂ)= ↑(0:ℝ); simp
  · change (0:ℂ)= ↑(directX G S 0 (i,j)); simp
  · change _=((directX G S ((directX G S).symm u) (i,j):ℝ):ℂ); rw [(directX G S).apply_symm_apply]; rfl
  change (0:ℂ)= ↑(0:ℝ); simp
lemma velvet_path : Turns (fun _ => velvetX S.patch) (orbitV (G:=G) S) := by
  refine ⟨spinGather (velvetX _),fun u => ?_,fun p q _ v => spinMoves _ p v⟩
  ext1 i; rcases i with ⟨i,j|(j|(j|j))⟩
  · change (0:ℂ)= ↑(0:ℝ); simp
  · change (0:ℂ)= ↑(directX G S 0 (i,j)); simp
  · change (0:ℂ)= ↑(directX G S 0 (i,j)); simp
  rfl
lemma atlas_photo {W} {Φ : Bridge G S.patch} (h : Premise S W Φ) : Turns (arriving Φ) (atlasQ S W) := by
  classical
  let T := unitSplit G S 1
  let M := repackM T (Equiv.refl _) (patron G W)
  let H : Phase (Lines G c 1) →ₗ[ℂ] Phase (Co c (Co S.patch.L (Loc G 1))) := Matrix.mulVecLin (approached M)
  let K : Phase (Lines G c 1) →ₗ[ℂ] Phase (Co c (Acts G S.patch)) := {
    toFun x := fun i => arranging S.patch (fun j => x (i.1,j)) 0 (Sum.elim (fun j => H x (i.1,j)) 0) 0 i.2
    map_add' a b := by ext1 i; simp only [map_add]; rcases i with ⟨i,j|((j|j)|(j|j))⟩ <;> simp [arranging]
    map_smul' a b := by ext1 i; simp only [map_smul]; rcases i with ⟨i,j|((j|j)|(j|j))⟩ <;> simp [arranging] }
  refine ⟨K,fun i => ?_,fun p q he v => ?_⟩
  · have hx : H (axes i)=axes (M*ᵥ i) := prom_vec ..
    ext1 j; rcases j with ⟨u,j|((j|j)|(j|j))⟩
    · rfl
    · let y := T.symm (u,j)
      have ht : T y=(u,j) := T.apply_symm_apply _
      have hy : clothe G S (.inl y)=(u,.inl j) := by rw [inflowL]; simp only [show unitSplit G S 1 y= _ from ht] <;> rfl
      have hY : (M*ᵥ i) (u,j)=uniformM W i y := by
        rw [show M*ᵥ i=(patron G W*ᵥ i)∘T.symm from repack_act T (Equiv.refl _) (patron G W) i,patron_fee]; rfl
      change H (axes i) (u,j)= ((directX G S (endorse W i) (u,.inl j):ℝ):ℂ); rw [hx, ← hy, direct_in]; exact congr_arg (fun x : ℝ => (x:ℂ)) hY
    ·
      change (0:ℂ)= ((directX G S (endorse W i) (u,.inr j):ℝ):ℂ); rw [direct_high]; change (0:ℂ)= ↑(0:ℝ); simp
    · change (0:ℂ)= ↑(directX G S 0 (u,j)); simp
    change (0:ℂ)= ↑(0:ℝ); simp
  have hh : H (tune p v)= tune p (Φ q*ᵥ v) := by
    have hl := h p q he v; rw [add_zero] at hl; exact hl
  ext1 j
  rcases j with ⟨i,j|((j|j)|(j|j))⟩ <;> simp [tune,K,arranging,arriving, hh]
end arc
end YM.Stationary
end
