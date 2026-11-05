import YM.WilsonBulk.Web.Pager

set_option autoImplicit false
noncomputable section
namespace YM.WilsonBulk.Sheet
open scoped Topology Classical ENNReal BigOperators
open Function Equiv Lattice Bloch Pert.Bulk
variable {X Y α β γ : Type} {c d : Side} {n m k : ℕ} {σ θ p q : ℝ} {D : Rule X}

section pluck
variable {Λ : X→Y} {x : X} {v : Legs Y n} {i : Fin n}

-- grouping by the image of the leading argument in the finite-volume seam
-- pluck. Each fiber is the full page for hitch y v.
def rollup (y : Y) :
    {a : X × Thesis Λ i x v // Λ a.1=y} ≃ Thesis Λ i.succ x (hitch y v) where
  toFun a := ⟨hitch a.val.1 a.val.2.val, by rw [hitch_succ,hitch_comp]; exact ⟨a.val.2.property.1, by rw [a.property, a.val.2.property.2]⟩⟩
  invFun a := ⟨(a.val 0,⟨crop a.val, by
    refine ⟨a.property.1, ?_⟩; exact funext fun i=> by
      simpa only [crop,hitch_succ,comp_apply] using (congr_fun a.property.2 i.succ)⟩), by
        change (Λ ∘ a.val) 0=y
        rw [a.property.2,hitch_zero]⟩
  left_inv z := Subtype.ext (Prod.ext (hitch_zero z.val.1 z.val.2.val) (Subtype.ext (crop_hitch z.val.1 z.val.2.val)))
  right_inv z := Subtype.ext (hitch_crop z.val)

def liftingOne (u : Legs Y n) (x : X) (i : Fin n) (Λ : X→Y) : X × Thesis Λ i x u ↪ Legs X (n+1) where
  toFun a:= hitch a.1 a.2.val
  inj' a b h:= by
    refine Prod.ext (congr_fun h 0) (Subtype.ext ?_)
    simpa using congr_arg crop h

lemma pluck_income (u : Page X (n+1)) (h : Within D σ p u) (hp : 0≤σ) :
    Summable fun a:X×Thesis Λ i x v => u (hitch a.1 a.2.val) := by
  refine ((within_total h hp i.succ x).comp_injective (liftingOne _ _ _ Λ).injective).congr (fun a => ?_)
  change (if hitch a.1 a.2.val i.succ=x then _ else (0:ℝ))=_
  rw [hitch_succ,if_pos a.2.property.1]; rfl
lemma Orates.pluck {u : Page X (n+1)} {V : Page Y (n+1)} (he : Orates Λ u V) (h : Within D σ p u) (hp : 0≤σ) :
    Orates Λ (pluck u) (pluck V) := by
  intro i x v hx
  let s := fun a:X×Thesis Λ i x v=> u (hitch a.1 a.2.val)
  have H : Summable s := pluck_income u h hp
  let k : X×Thesis Λ i x v→ Y := Λ ∘ Prod.fst
  have hz (y : Y) : V (hitch y v) = ∑' a:{a//k a=y},s a.val := by
    rw [he i.succ x (hitch y v) (by simp [hx])]
    exact ((rollup (x:=x) (i:=i) (v:=v) (Λ:=Λ) y).tsum_eq (fun a => u a.val)).symm
  change (∑' y,V (hitch y v)) = ∑' b : Thesis Λ i x v, ∑' y : X,u (hitch y b.val)
  rw [tsum_congr hz]
  refine Eq.trans (H.hasSum.tsum_fiberwise k).tsum_eq ?_
  exact ((Equiv.prodComm (Thesis Λ i x v) X).tsum_eq s).symm.trans H.prod_symm.tsum_prod
end pluck

section seam
variable {Λ : X→Y} {i : Fin n} {x : X}
abbrev Trail (Λ : X→Y) (a : Legs Y n) := {v : Legs X n// Λ ∘ v=a}
def pinned (a : Legs Y n) (x : X) : Trail Λ a ≃ Thesis Λ 0 x (hitch (Λ x) a) where
  toFun v := ⟨hitch x v.val, ⟨hitch_zero .., by rw [hitch_comp,v.property]⟩⟩
  invFun v := ⟨crop v.val, by rw [← crop_comp,v.property.2,crop_hitch]⟩
  left_inv v := Subtype.ext (crop_hitch x v.val)
  right_inv v := by apply Subtype.ext; change hitch x (crop v.val)= v.val; exact congr_arg (fun y=> hitch y (crop v.val)) v.property.1 |>.symm.trans (hitch_crop ..)
def spine (a : Legs Y k) (b : Legs Y n) : (Trail Λ a × Trail Λ b) ≃ Trail Λ (Fin.append a b) where
  toFun v := ⟨Fin.append v.1.val v.2.val, by rw [append_comp,v.1.property,v.2.property]⟩
  invFun v := (⟨snip k n v.val, by rw [← snip_comp,v.property,snip_append]⟩,
               ⟨keep k n v.val, by rw [← keep_comp,v.property,keep_append]⟩)
  left_inv v := Prod.ext (Subtype.ext (snip_append ..)) (Subtype.ext (keep_append ..))
  right_inv v := Subtype.ext (append_back ..)
lemma bind_pin (u : Page X (n+1)) (x : X) (a : Legs Y n) : page Λ 0 x u (hitch (Λ x) a) = ∑' v:Trail Λ a,u (hitch x v.val) := ((pinned (Λ:=Λ) a x).tsum_eq (fun q:Thesis ..=> u q.val)).symm
lemma pin_paid (u : Page X (n+1)) (x : X) (a : Legs Y n) (h : Within D σ p u) (hp : 0≤σ) : Summable fun v : Trail Λ a=>u (hitch x v.val) :=
    ((pinned (Λ:=Λ) a x).summable_iff (f:=fun q:Thesis ..=>u q.val)).mpr (page_money Λ u h hp 0 x _)
lemma seam_period {u : Page X (k+1)} {v : Page X (n+1)} (hu : Within D σ p u) (hv : Within D θ q v) (hp : 0 ≤ σ) (hq : 0≤θ)
    (x : X) (w : Legs Y (k+n)) :
    page Λ 0 x (seam u v) (hitch (Λ x) w) = page Λ 0 x u (hitch (Λ x) (snip k n w))* page Λ 0 x v (hitch (Λ x) (keep k n w)) := by
  refine legs_plus (k:=k) (fun w=> page Λ 0 x (seam u v) (hitch (Λ x) w)=page Λ 0 x u (hitch (Λ x) (snip k n w))*page Λ 0 x v (hitch (Λ x) (keep k n w))) ?_ w; intro a b
  rw [snip_append,keep_append,bind_pin, bind_pin,bind_pin,← (spine (Λ:=Λ) a b).tsum_eq _]
  let g := fun z : Trail Λ a=>u (hitch x z.val); let f:=fun z:Trail Λ b=> v (hitch x z.val)
  have he : Summable g:= pin_paid u x a hu hp; have hh : Summable f := pin_paid v x b hv hq
  change (∑' z:Trail Λ a × Trail Λ b,seam u v (hitch x (Fin.append z.1.val z.2.val)))=(∑' z,g z)*(∑' z,f z)
  rw [show _ = ∑' z:Trail Λ a × Trail Λ b,g z.1 * f z.2 from tsum_congr fun z=> seam_apply u v x z.1.val z.2.val]
  exact (tsum_mul_tsum_of_summable_norm he.norm hh.norm).symm

lemma Orates.sewn {u : Text α (k+1)} {v : Text α (n+1)} {U V}
    (hu : Orates (small c α) u U) (hv : Orates (small c α) v V) (pU : Pervasive u) (pV : Pervasive v)
    (h : Within (lawn α) σ p u) (he : Within (lawn α) θ q v) (hp : 0≤σ) (hq : 0 ≤ θ) :
    Orates (small c α) (seam u v) (seam U V) := by
  refine Orates.one (pU.sewn pV) 0 ?_
  intro w; refine legs_succ (fun w:Legs (Co c α) (k+n+1)=> ∃ x,w 0=small c α x ∧ seam U V w = page (small c α) 0 x (seam u v) w) ?H w
  case H =>
    intro x y
    obtain ⟨a,rfl⟩ := small_onto c α x
    refine ⟨a,hitch_zero ..,?_⟩
    rw [seam, hitch_zero, crop_hitch, hu 0 a _ (hitch_zero ..), hv 0 a _ (hitch_zero ..), seam_period h he hp hq]
end seam
section pairs
-- one-row exact alignment with `Row.acts`
def tailOne (w : Co c α) : Trail (small c α) (fun _:Fin 1=>w) ≃ {x : Cover// wrap c x=w.1} where
  toFun x := ⟨(x.val 0).1,by have he:= congr_arg Prod.fst (congr_fun x.property 0); exact he⟩
  invFun p := ⟨fun _=>(p.val,w.2), funext fun _=> Prod.ext p.property rfl⟩
  left_inv x := by apply Subtype.ext; ext1 i; rw [Fin.fin_one_eq_zero i]; exact Prod.ext rfl (by have he:= congr_arg Prod.snd (congr_fun x.property 0); exact he.symm)
  right_inv _ := Subtype.ext rfl
lemma page_one (Λ : Text α 2) (x : Market α) (w : Co c α) : page (small c α) 0 x Λ (two (small c α x) w)= ∑' y:Cover, if wrap c y=w.1 then Λ (two x (y,w.2)) else 0 := by
  rw [two,bind_pin,← (tailOne w).symm.tsum_eq _]
  refine Eq.trans (tsum_subtype {y|wrap c y=w.1} (fun y=>Λ (two x (y,w.2)))) ?_
  apply tsum_congr; intro y; rw [Set.indicator_apply]; simp only [Set.mem_setOf_eq]
variable [Fintype α]
lemma plain_orates (T : Row α α) : Orates (small c α) (pair (plain T)) (pair (fun x y=> T.acts c x y)) := by
  apply Orates.one (Pervasive.plain_pair T) 0
  intro v; obtain ⟨x,hx⟩:= small_onto c α (v 0)
  refine ⟨x,hx.symm,?_⟩
  let a:= v 1
  have hz : v=two (small c α x) a:= funext fun i=> by fin_cases i <;> first| exact hx.symm | rfl
  calc
    pair _ _ = display (plain T) c x a := by
                  rw [pair, ← hx]; exact (matches_plain T x a).symm
    _ = page (small c α) 0 x (pair (plain T)) (two (small c α x) a) := (page_one (pair (plain T)) x a).symm
    _ = _ := by rw [hz]
end pairs
end YM.WilsonBulk.Sheet
