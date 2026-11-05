import YM.WilsonBulk.Broadcast.Profiles
import YM.AnalyticNext.QUARTIC_MATCH.Multiples

/-!
# Descent of full Ward identities by multiples (not selecting special physical periods)

A qualifier period C may never fit the purchase threshold, but witness truth
of a Ward identity about COVER kernels can be tested by repetition into
arbitrarily large periods. We have exact lesson on multiplying OR-gauge
poly eval; image-winding not assumed negligible except pointwise and
cost transfer via `Proxy`. Needed to keep nonlinear Ward identities across
re-establishing cover costs.
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonBulk.Sheet.Hallmark
open Function Lattice Laurent Bloch Pert.Bulk Equiv Finset Filter
open AnalyticNext.QuarticMatch.Sheets
open scoped Topology BigOperators ENNReal Classical
variable {X Y Z α β γ : Type} {p q σ : ℝ} {n d i : ℕ} {c f Λ : Side}

-- Fiberwise exact transitive
abbrev harbor (α : Type) (h : c.val∣ f.val) : Co f α → Co c α := fun x=> (project h x.1,x.2)
lemma tides (α : Type) (h : c.val∣ f.val) : harbor α h ∘ small f α=small c α := funext fun _ => Prod.ext (project_wrap _ _) rfl
lemma count_site (h : c.val∣f.val) [Fintype α] [AddCommMonoid X] (F : Co c α→ X) : ∑ v,F (harbor α h v)= mult h • ∑ v,F v:= count_extra ..

lemma descendant [Fintype Y] (U : Page X (n+1)) (F : X→ Y) (G : Y→ Z) (v : Legs Z n) (x : X)
    {D : Rule X} (hu : Within D σ p U) (he : 0 ≤ σ) :
    ∑' (a:Trail (G ∘ F) v), U (hitch x a.val) = ∑ b:Legs Y n,if G ∘ b=v then ∑' a:Trail F b, U (hitch x a.val) else 0 := by
  let K : Legs X n→ℝ:=fun a=> if G ∘ (F ∘ a)=v then U (hitch x a) else 0
  have heq : Summable (fun a:Legs X n => U (hitch x a)):= (within_total hu he 0 x).comp_injective (i:=hitch x) (fun a b h=> by simpa using congr_arg crop h)|>.congr (fun i=> by simp [Function.comp])
  have hK : Summable K:= by apply Summable.congr (heq.indicator {a|G ∘ (F ∘ a)=v}) (fun i=>?_); simp only [K,Set.indicator_apply,Set.mem_setOf_eq]
  rw [show ∑' a:Trail (G ∘ F) v,U (hitch x a.val) = ∑' z,K z from ?_]
  swap
  · refine Eq.trans (tsum_subtype {a| (G ∘ F) ∘ a=v} (fun a=> U (hitch x a))) ?_; exact tsum_congr fun z=> by rw [Set.indicator_apply]; rfl
  rw [event_tsum hK F,tsum_fintype]; apply sum_congr rfl; intro b _
  split
  next hv=> exact tsum_congr fun a=> by unfold K; rw [a.property,if_pos hv]
  next hk=> exact (tsum_congr (fun a:Trail F b=> show K a.val=0 from if_neg (by rw [a.property]; exact hk))).trans tsum_zero
lemma page_down (V : Text α (n+1)) (h : c.val∣f.val) {U : Page (Co f α) (n+1)} {W : Page (Co c α) (n+1)} [Fintype α] (hu : Orates (small f α) V U) (hw : Orates (small c α) V W) (hv : Within (lawn α) σ p V) (he : 0≤σ) (i : Co f α) (u : Legs (Co c α) n) :
    W (hitch (harbor α h i) u)= ∑ a:Legs (Co f α) n,if harbor α h ∘ a=u then U (hitch i a) else 0:= by
  obtain ⟨x,rfl⟩:= small_onto f α i
  rw [show harbor α h _= _ from congr_fun (tides α h) x,quota_page hw x u rfl, ← tides α h, descendant V _ _ u x hv he]; exact sum_congr rfl fun a _=> by rw [quota_page hu x a rfl]; congr! -- duplicate rewrites?
-- sum fibre no kernel proof N for tiny C≥... supplied. `rename` semantics.
variable [Fintype α]
open MvPolynomial (C X)
lemma rename_hush (h : c.val∣f.val) {V : Text α (n+1)} {U : Page (Co f α) (n+1)} {W : Page (Co c α) (n+1)} (hu : Orates (small f α) V U) (hw : Orates (small c α) V W) (hv : Within (lawn α) σ p V) (he : 0≤σ) :
    MvPolynomial.rename (harbor α h) (script U) = mult h • script W := by
  let l:=harbor α h
  rw [script_trace U,script_trace W,map_sum]; rw [← count_site h]; apply sum_congr rfl; intro i _; rw [map_mul,MvPolynomial.rename_X]; congr 1
  simp only [script,map_sum,field,map_mul,map_prod,margin, MvPolynomial.rename_X,MvPolynomial.rename_C,page_down V h hu hw hv he,sum_mul]; rw [sum_comm]; refine sum_congr rfl fun a _=>?_
  simp [apply_ite,ite_mul]
-- down printed limit from Proxy via fixed period smearing
lemma coupon_limit {K : ℕ→ Text α n} {U : Text α n} (h : ∀ᶠ i in atTop, Within (lawn α) σ p (K i))
    (hv : 0<σ) (he : Tendsto K atTop (𝓝 U)) (u : Legs (Co f α) n) : Tendsto (fun i=> coupon f n (K i) u) atTop (𝓝 (coupon f n U u)) := by
  cases n; exact tendsto_const_nhds; rename_i n
  let x : Market α:= (lift (u 0).1,(u 0).2)
  let P (z : Text α (n+1)) (a : Thesis (small f α) 0 x u) := z a.val
  let w (a : Legs (Market α) (n+1)) := p*Real.exp (-σ*run (lawn α) x a)
  have hz : Summable w := (expo_all hv x _).mul_left p
  refine tendsto_tsum_of_dominated_convergence (f:=fun i=> P (K i)) (g:= P U) (hz.subtype _) (fun a=> (tendsto_pi_nhds.mp he a.val)) ?_
  refine h.mono fun i hi v=>?_
  exact item_bound hi 0 v.val |>.trans_eq (by rw [v.property.1]; rfl)
end YM.WilsonBulk.Sheet.Hallmark
