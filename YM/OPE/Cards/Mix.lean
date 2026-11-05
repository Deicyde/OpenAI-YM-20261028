import YM.OPE.Cards.Scale

/-!
# Complete Deck: mixed chessboard price in many distant translations
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Cards
open Function Filter Set Lattice Cells Wilson Extraction Word Next.Phase
open Work Next.Rank Station Bid
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius
variable {G:Gauge}{C:Family G} {ι κ ξ : Type}[Fintype ι][Fintype κ] {S:Schedule}
    {φ : Extraction.Order} {𝓕 : Filter (ℕ×ℕ)}
variable {N p k k' b l f n w q Q : ℕ} {B:ι→ℝ}{D:κ→ℝ}
    (e:b≤ k)(t m:ℕ) {x:ι→ Cover}{y:κ→ Cover}

-- norm here Euclidean (could use cubedist with smaller constant)
def Gap (S : Schedule)(k:ℕ)(x:ι→ Cover)(A:ℝ):=∀ i j,i≠j→ A<‖S.gridPoint k (x i) - S.gridPoint k (x j)‖
def GapTo (S : Schedule)(k:ℕ)(x:ι→ Cover)(y:κ→ Cover)(A:ℝ):=∀ i j,A<‖S.gridPoint k (x i)-S.gridPoint k (y j)‖
def arrange (e : b ≤ k) (C:Family G) (t j:ℕ) (x : Cover) := x+ Episode.step C e t j
lemma Gap.instantiated (h:Gap C.S k x (2*C.S.a q)) : ∀ᶠ t:ℕ in atTop, ∀ᶠ i:ℕ ×ℕ in φ.fuse, ∀ hi:q≤ i.fst, ∀ j j':Fin m×ι,j≠j' → Cells.span C.S hi i.2< separation (location C.S k i.1 i.2 (arrange e C t j.1 (x j.2))) (location C.S k i.1 i.2 (arrange e C t j'.1 (x j'.2))) :=by
    have he : ∀ᶠ t:ℕ in atTop, ∀ j j':Fin m×ι, j≠j'→ 2*C.S.a q<‖C.S.gridPoint k (arrange e C t j.1 (x j.2))-C.S.gridPoint k (arrange e C t j'.1 (x j'.2))‖:= by
       refine eventually_all.mpr fun j=> eventually_all.mpr fun j'=> eventually_all.mpr fun hJ=> ?_
       rcases j,j' with ⟨⟨j,a⟩, k',s⟩ -- syntax multiple objects check
       by_cases he:j=k'; subst k'; · exact Eventually.of_forall fun _=> car_space_same e C _ (x a) (x s) (h a s (by rintro rfl; exact hJ rfl))
       exact car_space e C _ (x a) (x s) (Fin.val_injective.ne he)
    filter_upwards [he] with t ht; have hu:= eventually_all.mpr fun j=> eventually_all.mpr fun j'=> eventually_all.mpr fun h=> lock_space (φ:=φ) C q _ _ (ht j j' h)
    exact hu.mono fun i hi hk j j' h=>hi j j' h hk
lemma GapTo.instantiated (h:GapTo C.S k x y (2*C.S.a q)) : ∀ᶠ t:ℕ in atTop, ∀ᶠ i:ℕ ×ℕ in φ.fuse, ∀ hi:q≤ i.fst, ∀ (j:Fin m×ι) (j':Fin m×κ), Cells.span C.S hi i.2< separation (location C.S k i.1 i.2 (arrange e C t j.1 (x j.2))) (location C.S k i.1 i.2 (arrange e C t j'.1 (y j'.2))) :=by
    have he : ∀ᶠ t:ℕ in atTop, ∀ (j:Fin m×ι) (j':Fin m×κ), 2*C.S.a q<‖C.S.gridPoint k (arrange e C t j.1 (x j.2))-C.S.gridPoint k (arrange e C t j'.1 (y j'.2))‖:= by
       refine eventually_all.mpr fun ⟨j,a⟩=> eventually_all.mpr fun ⟨k',s⟩=>?_
       by_cases he:j=k'; subst k'; · exact Eventually.of_forall fun _=> car_space_same e C _ (x a) (y s) (h a s)
       exact car_space e C _ (x a) (y s) (Fin.val_injective.ne he)
    filter_upwards [he] with t ht; have hu:= eventually_all.mpr fun j=> eventually_all.mpr fun j'=> lock_space (φ:=φ) C q _ _ (ht j j')
    exact hu.mono (fun i hi hk j j'=> hi j j' hk)

abbrev Cylinder (C:Family G) := (N p:ℕ)→ Config G (C.side N p)→ℂ

def register (C:Family G) (k:ℕ)(u:ι→ Cover)(F:ι→Cylinder C)(N p : ℕ): Config G (C.side N p)→ℂ:=
    fun U=>∏ i, (F i N p ∘ translate (location C.S k N p (u i))) U
lemma register_step (s:Cover)(C:Family G)(x:ι→ Cover) {g:ι→Cylinder C} :
    register C k x g N p ∘ translate (location C.S k N p s)= register C k (fun i=> x i+s) g N p:=by
    funext u; unfold register; dsimp only [comp_apply]; refine Finset.prod_congr rfl fun i _=>?_ ; rw [← pull_one,← pull_one, pull_pull, Order.location_add, ← pull_one]; simp [affine]

structure Hall (S:Schedule)(b l k f n : ℕ) (p t : ℕ) : Prop where -- f buffer for seats, k' grid, n ext, k main
    first : b≤f
    second : f ≤ l
    third : f ≤ k
    fourth : l ≤ n
    paid : (p:ℝ)*(2*(5*S.a f)) < S.a b
    money : (t:ℝ)*(2*(3*S.a n)) < S.a l
-- k' placeholder? remove
lemma largeMesh (φ: Extraction.Order) : Tendsto Prod.fst φ.fuse atTop:= tendsto_atTop.mpr fun i=> show φ.late (fun N _=> i≤N) from Eventually.of_forall fun _=> φ.mesh.cofinal.eventually_ge_atTop i

def deck (C:Family G)(e:b≤k)(m t:ℕ) (Z : Cylinder C)(N p:ℕ) := moment (C.beta N p) (fun U=> ∏ j:Fin (2*m), if j.val%2=0 then star ((Z N p ∘ translate (location C.S k N p (Episode.step C e t j.val))) U) else (Z N p ∘ translate (location C.S k N p (Episode.step C e t j.val))) U)
variable {g:ι→ Cylinder C}{u: κ→ Cylinder C} {Z : Cylinder C}
lemma mixed (h:C.Makes)(hr:𝓕 ≤ φ.fuse)(hX:Gap C.S k x (2*C.S.a b)) (hh:Gap C.S k y (2*C.S.a l))(hS:GapTo C.S k x y (2*C.S.a b)) (hp:Hall C.S b l Q f n (Fintype.card ι) (Fintype.card κ))
    (hU:∀ j, ∀ᶠ i in 𝓕, PaidAt C.S i.1 i.2 Q (C.beta i.1 i.2) (B j) (g j i.1 i.2)) (hv:∀ j, ∀ᶠ i in 𝓕, PaidAt C.S i.1 i.2 n (C.beta i.1 i.2) (D j) (u j i.1 i.2))
    (he:∀ᶠ i in 𝓕,Z i.1 i.2=register C k x g i.1 i.2 * register C k y u i.1 i.2):
    ∀ᶠ t:ℕ in atTop, ∀ᶠ i in 𝓕, ‖deck C e m t Z i.1 i.2‖ ≤ ((∏ x,B x)*(∏ y,D y))^(2*m):=by
    have hN(a:ℕ): ∀ᶠ i:ℕ×ℕ in 𝓕, a ≤ i.1:= ((largeMesh φ).eventually_ge_atTop a).filter_mono hr
    filter_upwards [hX.instantiated (φ:=φ) e (2*m), hh.instantiated (φ:=φ) e (2*m), hS.instantiated (φ:=φ) e (2*m)] with t hx hy hS
    filter_upwards [hx.filter_mono hr,hy.filter_mono hr,hS.filter_mono hr,eventually_all.mpr hv,eventually_all.mpr hU,he,hN n,hN Q,hN k] with i hx hy hS hv hU he hz hG hk
    let N:=i.1; let p:=i.2; let H: l ≤ N:=hp.fourth.trans hz; let hf:f≤ N:= hp.second.trans H; let L:=location C.S k N p
    obtain ⟨o,hB,hD⟩:= seats C (p:=p) hf hp.first hp.second hp.fourth hz (L ∘ x) (L ∘ y) hp.paid hp.money
    let Y:=(center C.S p H 0).newly o; let T:= (center C.S p (e.trans hk) 0).newly o
    let Xj:= Fin (2*m)×ι; let Yj:=Fin (2*m)×κ
    let χ{J:Type}(x:J→ Cover)(w:Fin (2*m)×J) := L (arrange e C t w.1 (x w.2))
    let A{J:Type}(G:J→ Cylinder C)(w:Fin (2*m)×J)(U) := if w.fst.val%2=0 then star (G w.snd N p U) else G w.snd N p U
    have hI1(w:Xj):PaidAt C.S N p Q (C.beta N p) (B w.snd) (A g w):=by
       by_cases h:w.fst.val%2=0
       · simp only [h,if_true,A]; exact (hU _).stars
       simp only [h, ↓reduceIte,A]; exact hU _
    have hI2(w:Yj):PaidAt C.S N p n (C.beta N p) (D w.snd) (A u w):=by
       by_cases h:w.fst.val%2=0
       · simp only [h,if_true,A]; exact (hv _).stars
       simp only [h, ↓reduceIte,A]; exact hv _
    have hW:Y.side.val∣ T.side.val:= Around.inherits (hp.first.trans hp.second) H
    have hP:T.kind=.link:= rfl
    have hM (w:Xj):Inside T (3*Cells.span C.S hG p) (χ x w) := by
       apply invariantMargins e _ t (x w.2) hk (show T.kind=.link from rfl) (dvd_refl _) w.1.val
       have ht:= hB w.2; unfold Next.Phase.Inside; refine Lease.fewer T _ (Nat.mul_le_mul_left 3 (Nat.le_of_dvd (C.S.toDepth hf p).count.property ?_)) ht; exact Around.inherits hp.third hG
    have hZ:= plant (show Y.kind=.link from rfl) hP rfl hW hz (Around.inherits hp.fourth hz) hG (Around.inherits (hp.first.trans hp.third) hG) (χ y) (A u) (fun w=>D w.snd) (χ x) (A g) (fun w=>B w.snd)
       (fun j=>invariantMargins e _ t (y j.2) hk (show Y.kind=.link from rfl) hW j.1.val (hD _)) (hy H) hM (hx (e.trans hk)) (hS (e.trans hk)) hI2 hI1 (seamless h N p)
    let F{J:Type} [Fintype J] (x:J→ Cover) (g:J→Cylinder C) (U: Config G (C.side N p)) (w:Fin (2*m)):= ∏ i:J, A g (w,i) (translate (χ x (w,i)) U)
    let V U:= (∏ w,F x g U w)*∏ w,F y u U w; let a (w:ℕ)(U: Config G (C.side N p)):= Lattice.translate (location C.S k N p (Episode.step C e t w)) U
    have ht' (U:Config G (C.side N p)) : (∏ j:Fin (2*m), if j.val%2=0 then star (Z N p (a j.val U)) else Z N p (a j.val U))=V U:=by
       unfold V; rw [← Finset.prod_mul_distrib]; refine Finset.prod_congr rfl fun j _=>?_; rw [he]; let s:= Episode.step C e t j.val; let x':= fun i=> x i+s; let y':= fun i=>y i+s
       have hG' : register C k x g N p (a j.val U)= register C k x' g N p U:= congr_fun (register_step s C x) U; have hu': register C k y u N p (a j.val U)=register C k y' u N p U:= congr_fun (register_step s C y) U
       by_cases hp:j.val%2=0
       · simp only [hp,if_true,Pi.mul_apply]; rw [hG',hu']; simp only [hp,if_true,star_mul',F,A,register,star_prod]; rfl
       simp only [hp,if_false, Pi.mul_apply]; rw [hG',hu']; simp only [hp,if_false,F,A,register]; rfl
    have hφ : deck C e m t Z i.1 i.2= moment (C.beta N p) V:= congr_arg (moment (C.beta N p)) (funext ht')
    rw [hφ]; simp_rw [Fintype.prod_prod_type] at hZ; refine le_trans hZ ?_; simp [mul_pow]
end YM.OPE.Cards
