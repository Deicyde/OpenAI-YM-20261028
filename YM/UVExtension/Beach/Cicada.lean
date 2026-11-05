import YM.UVExtension.Beach.Ice
set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Beach
open Function Filter Set Metric Lattice RG Wilson
open Extraction Fallow Poppy Tide Swell Lamppost Spire Pier Rafter BoundedContinuousFunction MeasureTheory
open scoped Topology BigOperators Classical ContDiff
variable {a:ℝ} (ha:0<a)
local notation "V"=> Row a
local notation "Z"=> ball (0:ℂ) a
section
variable {n m:ℕ}
lemma climb_hol (v:ℂ→ Tabletop n→ℂ)(hv:∀ x,DifferentiableOn ℂ (fun z=> v z x) Z) (l:List (Axel n))(t:ℝ) (x:Tabletop n): DifferentiableOn ℂ (fun z=>rake t (v z) l x) Z:= by
    induction l generalizing x with
    | nil=>exact hv _
    | cons a l ih=> exact ((ih (x+hike a)).sub (ih x)).const_mul _
-- relative EqOn.Ban.F lemma
variable {A: Type} [MetricSpace A] {U:Set A}{f g:ℂ→ A →ℂ}{F:ℕ→ℂ→ A→ℂ}
lemma Stamp.align (h:Stamp a U f F)(he:∀ z∈ Z,EqOn (f z) (g z) U): Stamp a U g F :=by
   refine ⟨fun x hx=>?_,fun S hS hs=> ?_,fun K hK hD S hs ht j ε hp=>(h.converges K hK hD _ hs ht j ε hp).mono fun i hi z hz x hx=>?_⟩
   · exact ((h.analytic x hx|>.differentiableOn).congr (fun v hv=> (he v hv hx).symm)).analyticOnNhd isOpen_ball
   · obtain ⟨w,hw,H,hV⟩:= h.debt S hS hs; exact ⟨w,hw,H,fun x y hy=> (he y hy (hS x.2)|>.symm).trans (hV x hy)⟩
   have hm:(fun z=>f z x)=ᶠ[𝓝 z] fun z=>g z x:=Eventually.mono (p:=fun t=>t∈Z) (isOpen_ball.mem_nhds (hD hz)) fun _ h=> he _ h (ht hx)
   exact hm.iteratedDeriv_eq j ▸ hi z hz x hx
variable {U:Set (Points n)} (h:IsOpen U)(S:Schedule)(W:ℕ→ ℂ→ Tabletop n →ℂ)(Q: Row a→ Points n→ℂ)
variable (hf:∀ᶠ i in atTop,∀ x:Tabletop n,DifferentiableOn ℂ (fun z=> W i z x) (Metric.ball (0:ℂ) a))(hw:∀ l:List (Axel n),l.length≤ m→∀ K:Set (Points n),IsCompact K→K⊆U → ∃ M:ℝ,0 ≤ M∧ ∀ᶠ i in atTop,∀ z∈Metric.ball (0:ℂ) a,∀ x: Tabletop n,Extraction.tag (S.a i) x∈K→ ‖rake (S.a i) (W i z) l x‖ ≤ M)
    (hQ:∀ d:Row a,∀ (l:List (Axel n)),l.length ≤ m→ Meets U (Ink S (fun i=> rake (S.a i) (W i d.val) l)) (ivy (Q d) l)) (hx :∀ d:Row a,∀ (l:List (Axel n)),l.length < m→∀ x∈U,∀ i:Axel n,HasDerivAt (fun t:ℝ=> ivy (Q d) l (x+t • Points.direction i.1 i.2)) (ivy (Q d) (i::l) x) 0)
set_option quotPrecheck false
local notation "X"=> Tabletop n
include h ha hf hw
lemma ratesK (l:List (Axel n))(hl:l.length≤ m)(K:Set (Points n))(hk:IsCompact K)(hK:K⊆U)(y:X):∃ M:ℝ,0≤M∧∀ᶠ i in atTop,∀ z∈ Z,∀ x∈ K, ‖rake (S.a i) (W i z) l (Extraction.address (S.a i) x+y)‖≤ M:=by
    obtain ⟨r,hr,hR⟩:= hk.exists_cthickening_subset_open h hK; let c:ℝ:=4*n+‖tag 1 y‖; obtain ⟨M,hM,hQ⟩:=hw l hl _ hk.cthickening hR; have hh:Tendsto (fun i=> S.a i*c) atTop (𝓝 0):=by simpa using! S.shrinks.mul_const c
    refine ⟨M,hM,?_⟩; filter_upwards [hh.eventually (ge_mem_nhds hr),hQ] with i hi H z hz x hx; apply H z hz; apply mem_cthickening_of_dist_le _ _ _ _ hx
    let t:= S.a i; let A:= Extraction.address t x; rw [tagAdd]; refine (dist_triangle _ (tag t A) _).trans ((add_le_add_right (approximate (S.a_pos i) x) _).trans (le_trans ?_ hi)); rw [dist_eq_norm,add_sub_cancel_left,Poppy.tagRank (S.a i) y,norm_smul,Real.norm_of_nonneg (S.a_pos _|>.le)]; unfold c; apply le_of_eq; ring

def rails (l:List (Axel n))(i:ℕ)(z:ℂ):= Ink S (fun i=> rake (S.a i) (W i z) l) i
def tideL (l:List (Stride n))(i:ℕ)(z:ℂ):= interpolate (S.a i) (strides (S.a i) (W i z) l)
-- stamp with spatial continuum derivatives.Real & complex.
include hQ hx
structure Terrace (l:ℕ)(W:ℕ→ℂ→Tabletop n→ℂ)(a:ℝ)(U:Set (Points n))(F:ℂ→ Points n→ℂ) : Prop where
    loop(L:List (Axel n)): L.length≤ l→ Stamp a U (fun z=>ivy (F z) L) (rails S W L)
    walk(z:ℂ)(L:List (Axel n)) (i:Axel n) (x:Points n): L.length < l→ z∈Metric.ball (0:ℂ) a→ x∈U → HasDerivAt (fun t:ℝ=>ivy (F z) L (x+t • Points.direction i.1 i.2)) (ivy (F z) (i::L) x) 0
    wand(L:List (Stride n)): L.length≤ l → Stamp a U (fun z=> ivy (F z) (L.map Stride.axis)) (tideL S W L)

private lemma lane (l:List (Stride n))(hl:l.length ≤ m) : ∃ f:ℂ→ Points n→ℂ, Stamp a U f (tideL S W l) ∧ ∀ d:Row a, EqOn (f d.val) (ivy (Q d) (l.map Stride.axis)) U:=by
   let u:=l.map Stride.axis; have hv: u.length≤ m:=by simpa only [u,List.length_map] using hl
   obtain ⟨J,L,g,c,hc,hF⟩:=Poppy.ancestors l
   have hz(i z x): tideL S W l i z x=∑ t:Tiles n, (vote (S.a i) x t:ℂ) * ∑ j:J,c j * rake (S.a i) (W i z) u (Extraction.address (S.a i) x+ dropback t+g j):=by simp only [tideL,interpolate,hF (S.a i) (S.a_pos i),u]
   refine control ha _ _ (hf.mono fun i hi x=>?_ ) (fun K hK hk=>?_) ?_
   · change DifferentiableOn ℂ (fun z=> tideL S W l i z x) Z; simp_rw [hz]; refine DifferentiableOn.fun_sum fun t _=> DifferentiableOn.const_mul (DifferentiableOn.fun_sum fun j _=> DifferentiableOn.const_mul (climb_hol (W i) hi u _ _) _) _
   · choose M hM hX using fun t:Tiles n×J=> ratesK ha h S W hf hw _ hv K hk hK (dropback t.1+g t.2)
     let t (i:Tiles n):= ∑ j: J, ‖c j‖*M (i,j); have ht i: 0≤t i:= Finset.sum_nonneg (fun j _=>mul_nonneg (norm_nonneg _) (hM _))
     refine ⟨∑ i,t i,Finset.sum_nonneg (fun i _=> ht _),?_⟩; filter_upwards [eventually_all.mpr hX] with i hi z hz' x hx; rw [hz]; apply (norm_sum_le ..).trans (Finset.sum_le_sum (fun j _=>?_))
     have hp:=Poppy.voter (S.a i) x j; rw [norm_mul,Complex.norm_real,Real.norm_of_nonneg hp]; refine le_trans (b:= vote (S.a i) x j * t j) (mul_le_mul_of_nonneg_left ?_ hp) ?_
     · exact (norm_sum_le ..).trans (Finset.sum_le_sum fun l _=> (norm_mul ..).trans_le (mul_le_mul_of_nonneg_left (by rw [add_assoc]; exact hi (j,l) z hz' x hx) (norm_nonneg _)))
     exact mul_le_of_le_one_left (ht j) ((Finset.single_le_sum (fun i' _=> Poppy.voter (S.a i) x i') (Finset.mem_univ j)).trans_eq (Poppy.agrees ..))
   intro d; exact Poppy.uphol h (Poppy.stroke l h (F:=fun i=> W i d.val) (hQ d u hv))
lemma front :∃ f:ℂ→ Points n→ℂ,Terrace S m W a U f ∧ ∀ d: Row a,∀ l:List (Axel n), l.length ≤ m → EqOn (ivy (f d.val) l) (ivy (Q d) l) U := by
   have hv(l:List (Axel n))(hl:l.length≤ m): ∃ f:ℂ→ Points n→ℂ, Stamp a U f (rails S W l) ∧∀ d:Row a,EqOn (f d.val) (ivy (Q d) l) U:=by
       refine control ha (rails S W l) (fun d=>ivy (Q d) l) (hf.mono fun i hi x=> ?_) (fun K hK hk=>?_) (fun d=> hQ d l hl)
       · exact climb_hol (W i) hi _ _ _
       simpa only [rails,Ink] using! (by simpa only [add_zero] using! (ratesK ha h S W hf hw l hl K hk hK 0) : ∃ M:ℝ,0≤ M∧∀ᶠ i in atTop,∀ z∈ Z,∀ x∈ K,‖rake (S.a i) (W i z) l (Extraction.address (S.a i) x)‖≤ M)
   choose! f hh he using hv
   have hZ(z:ℂ)(l:List (Axel n))(i:Axel n)(hl:l.length < m)(hz:z∈ Z)(x:Points n)(hX:x∈U): HasDerivAt (fun t:ℝ=> f l z (x+t • Points.direction i.1 i.2)) (f (i::l) z x) 0:=by
        let Y:= Points.direction i.1 i.2; refine moved (S:=U) ha h (hh _ hl.le) (hh (i::l) (by exact hl)) Y x hX ?_ z hz; intro d y hy; rw [he _ (by exact hl) _ hy]; refine (hx d l hl y hy i).congr_of_eventuallyEq ?_; let g(t:ℝ):=y+t • Y; have hp: g ⁻¹' U ∈𝓝 0:= (show Continuous g by unfold g; fun_prop).continuousAt.preimage_mem_nhds (h.mem_nhds (by simpa [g])); exact Eventually.mono (p:=fun x=>g x∈ U) hp fun x hx=> he l hl.le d hx
   let G z:= f [] z
   have ht(l:List (Axel n))(hl:l.length≤ m)(z:ℂ)(hz:z∈Z): EqOn (f l z) (ivy (G z) l) U:=by
       induction l with
       | nil=> exact fun _ _=> rfl
       | cons i l ih=> intro x hx; let Y:= Points.direction i.1 i.2; let g(t:ℝ):= x+t • Y; have hp: g ⁻¹' U ∈𝓝 0:= (show Continuous g by unfold g; fun_prop).continuousAt.preimage_mem_nhds (h.mem_nhds (by simpa [g])); exact ((hZ z l i hl hz x hx).congr_of_eventuallyEq (Eventually.mono (p:=fun t=>g t∈ U) hp (fun t he=> Eq.symm (ih ((show l.length< m from hl).le) he))) |>.deriv).symm
   refine ⟨G,⟨fun L hl=>(hh L hl).align (ht _ hl),fun z L i x hL hz hX=>?_,fun L hl=>?_⟩,fun d L hl x hx=> ((ht L hl _ (desk a ha|>.within d) hx).symm.trans (he L hl d hx))⟩
   · let Y:= Points.direction i.1 i.2; let g(t:ℝ):=x+t • Y; rw [← show _ = _ from ht (i::L) hL z hz hX]; have hp:g ⁻¹' U∈𝓝 0:= (show Continuous g by unfold g; fun_prop).continuousAt.preimage_mem_nhds (h.mem_nhds (by simpa [g])); exact (hZ z L i hL hz _ hX).congr_of_eventuallyEq (Eventually.mono (p:=fun t=> g t∈ U) hp fun t he=> (ht L hL.le z hz he).symm)
   obtain ⟨y,hY,hG⟩:= lane ha h S W Q hf hw hQ hx _ hl -- hx perhaps unused
   let u:= L.map Stride.axis; have hm:u.length≤ m:=by simpa only [u,List.length_map]
   apply hY.align; intro z hz x hy
   have hv':= (desk a ha).agrees (fun z=>y z x) (fun z=> f u z x) (bumps _ _ (hY.analytic _ hy|>.differentiableOn)) (bumps _ _ ((hh u hm|>.analytic _ hy).differentiableOn)) (fun d=> (hG d hy).trans (he u hm d hy).symm) hz; exact hv'.trans (ht u hm z hz hy)
end
end YM.UVExtension.Beach
