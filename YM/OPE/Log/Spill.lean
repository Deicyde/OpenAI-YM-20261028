import YM.OPE.Schemes.Read
import YM.OPE.Log.Fees
/-!
# Swept cost also with variable representatives in a configuration at cutoff
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Log
open MeasureTheory Function Filter Set Lattice Cells Wilson Extraction Word
open Cards Bid Spec
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius
variable {G:Gauge}{C:Family G}{F : Extraction.Order}{S:Table C.book} (U: Final C F S)(h:Org.Grill C F)
variable {I J : Type}[Fintype I][Fintype J] {N p k f b l n q : ℕ}
variable {𝓕 : Filter (ℕ×ℕ)}
variable {B:I→ℝ}{D:J→ℝ} {x:I→ Cover}{v:I→ C.book.Token}{y:J→ Cover}{w:J→ C.book.Token}
    (Z:ReadLabel C v)(Y:ReadLabel C w)

variable {t:ℕ}{P: ℕ×ℕ→ C.label t}{a:C.label t}(o:ℝ)
local notation "Z0"=> (fun _ : Unit=> (0:Cover))
local notation "T'" => C.S.gridPoint k
include h
lemma unionMirror {X:ReadLabel C v}(hX:∀ i,Tendsto (X i) 𝓕 (𝓝 (v i).2))(hk:b ≤ k)(hp:Gap C.S k y (2*C.S.a l))(hd:GapTo C.S k (Z0) y (2*C.S.a b))
    (hf:Screen (beside ((T') ∘ x) ((T') ∘ y)))
    (hx:Screen (beside ((T') ∘ Z0) ((T') ∘ y)))
    (he:Hall C.S b l q f n 1 (Fintype.card J)) [𝓕.NeBot] (hr:𝓕≤ F.fuse)(hz:Tendsto P 𝓕 (𝓝 a))
    (hB : ∀ᶠ i:ℕ×ℕ in 𝓕, PaidAt C.S i.1 i.2 q (C.beta i.1 i.2) o (register C k x (germ X) i.1 i.2 - C.O i.1 i.2 (P i) 0))
    (hD:∀ j, ∀ᶠ i:ℕ×ℕ in F.fuse,PaidAt C.S i.1 i.2 n (C.beta i.1 i.2) (D j) (C.O i.1 i.2 (d:=(w j).1) (w j).2 0)) :
    ‖viewing U (beside ((T') ∘ x) ((T') ∘ y)) (beside v w) - viewing U (beside ((T') ∘ Z0) ((T') ∘ y)) (beside (fun _ : Unit=>⟨t,a⟩) w)‖ ≤ o * ∏ i,D i:=by
    let G := X; let Y' := frozen C w; let V (_ : Unit):C.book.Token:= ⟨t,a⟩; let W:ReadLabel C V:= fun _=>P; rw [← beside_commutes] at hf hx; rw [← beside_commutes,← beside_commutes]
    let S:Cylinder C:=fun N p=> register C k x (germ G) N p - C.O N p (P (N,p)) 0; have hv(j): Tendsto (combine G Y' j) 𝓕 (𝓝 ((beside v w j).2)):=by cases j ; exact hX _; exact tendsto_const_nhds
    have hu(j):Tendsto (combine W Y' j) 𝓕 (𝓝 ((beside V w j).2)):=by cases j; exact hz; exact tendsto_const_nhds
    have hl: Gap C.S k Z0 (2*C.S.a b):=fun i j h=> (h (Subsingleton.elim ..)).elim
    have hQ: TileDoc U k 𝓕 (viewing U ((T') ∘ beside x y) (beside v w) - viewing U ((T') ∘ beside Z0 y) (beside V w))
        (register C k (beside x y) (germ (combine G Y')) - register C k (beside Z0 y) (germ (combine W Y'))):= TileDoc.diff U hf hx hv hu
    apply le_trans (TileDoc.global U hQ (B:=fun _ : Unit=>o) h hk hr hl hp hd he (z:=fun _=> S) (w:=germ Y') (fun _=> hB) (fun j=> (hD j).filter_mono hr) ?_) (by simp)
    filter_upwards with i; let R:Cylinder C:= fun N p=> C.O N p (P (N,p)) 0; simp only [Pi.sub_apply]
    rw [works,works, just_one S, show germ W =(fun _=>R) from rfl, just_one R]; unfold S; rw [sub_mul]
variable {Z' Z'': J→ E4} {A:ℝ}
local notation "z0"=> (fun _ : Unit=> (0:E4))
omit h
structure Stylus {v:I→ C.book.Token} (X:ReadLabel C v) (𝓕: Filter (ℕ×ℕ)) (k f d : ℕ)(x : I→ Cover)(q:ℕ×ℕ→ C.label d)(A:ℝ) : Prop where
    receipt : ∀ᶠ i:ℕ×ℕ in 𝓕, Cards.PaidAt C.S i.1 i.2 f (C.beta i.1 i.2) A (Cards.register C k x (germ X) i.1 i.2 - C.O i.1 i.2 (q i) 0)

include h in
lemma stylus_admits {Y₀: ReadLabel C v} (h0:∀ i,Tendsto (Y₀ i) 𝓕 (𝓝 (v i).2))(hk:b ≤ k)(hh: Screen (T' ∘ x))(hp: Apart (2*C.S.a l) Z')(hd:ApartFrom (2*C.S.a b) z0 Z') (hT:Injective (beside ((T') ∘ x) Z'))
    (he:Cards.Hall C.S b l q f n 1 (Fintype.card J)) [𝓕.NeBot] (hr:𝓕 ≤ F.fuse)(hz:Tendsto P 𝓕 (𝓝 a))
    (hB: Stylus Y₀ 𝓕 k q t x P A)(hD: Prepared (C:=C) w F n D) :
    ‖viewing U (beside (T' ∘ x) Z') (beside v w) - viewing U (beside z0 Z') (beside (fun _ : Unit=>⟨t,a⟩) w)‖ ≤ A * ∏ i,D i:=by
    classical
    let W:= insert (0:E4) (Finset.univ.image fun i=> (T') (x i)); let z i:= Cloud.unitGrid C.S i W Z'; let y(i:ℕ):= Cloud.grid W (C.S.a i) Z' (fun _ _=>0); let V (_ : Unit):C.book.Token:= ⟨t,a⟩
    have hZ:Tendsto z atTop (𝓝 Z'):= Cloud.gridded W _ _; have hS(i): Screen (z i):= Cloud.screened _ _ (C.S.a_pos _) _ _
    have hx(k' i):∀ a,∀ y∈W,z k' i a≠y a:= fun a=> Cloud.clears _ _ (C.S.a_pos k') _ i a (fun _ _=>0)
    have hY: Injective (fun _:Unit=> (0:E4)):= injective_of_subsingleton _ -- remove i
    have hA(k): 0≤ 2*C.S.a k:=mul_nonneg zero_le_two (C.S.a_pos _|>.le)
    have hu:= hd.together (hA _) hY (hp.coin (hA _)); apply (glance_contract U (mul_nonneg hB.receipt.exists.choose_spec.cost hD.cost)).mpr; intro u
    rw [map_sub,glance_sees _ _ _ _ hT,glance_sees _ _ _ _ hu]
    let S':= spectator U u; have hv:=(spectate U u).smooth
    refine le_of_tendsto (((Tendsto.sub ((smooth_observe S' hv (beside v w) hT).tendsto.comp (Cloud.beside_tends (show Tendsto (fun t:ℕ=> (T') ∘ x) atTop _ from tendsto_const_nhds) hZ)) ((smooth_observe S' hv (beside V w) hu).tendsto.comp (Cloud.beside_tends (show Tendsto (fun t:ℕ=> z0) atTop _ from tendsto_const_nhds) hZ)))).norm) ?_
    filter_upwards [apart_limit hZ hp,cross_limit (show Tendsto (fun t:ℕ=> z0) atTop _ from tendsto_const_nhds) hZ hd,eventually_ge_atTop k] with i hψ hκ hi
    have hG:Screen (beside ((T') ∘ x) (z i)):= Screen.reserve.mpr ⟨hh,hS i,fun a b s h=> hx _ _ _ _ (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ (Finset.mem_univ a))) h.symm⟩; have hQ:Screen (beside z0 (z i)):= Screen.reserve.mpr ⟨(fun _=> injective_of_subsingleton _), hS i,fun a b s h=>hx _ _ _ _ (Finset.mem_insert_self ..) h.symm⟩
    change ‖observe _ (beside _ (z i)) _ - observe _ (beside _ (z i)) _‖ ≤ _
    rw [← glance_sees U u _ _ hG.coin, ← glance_sees U u _ _ hQ.coin,← map_sub]; apply le_trans (glance_bound ..) ?_
    have hc := (show (C.S.gridPoint i) ∘ (fun _ : Unit=> (0:Cover))=z0 from funext fun _=> grid_zero ..)
    have hK := (show C.S.gridPoint i ∘ zoom C.S hi ∘ x=(T') ∘ x from funext fun _=> zoom_grid hi _)
    rw [← hK,← hc]
    refine unionMirror U h A h0 (x:=zoom C.S hi ∘ x) (y:=y i) (hk.trans hi) hψ ?_ (hK.symm ▸ hG) (hc.symm ▸ hQ) he hr hz ?_ hD.here
    · change ApartFrom _ ((C.S.gridPoint i) ∘ _) (z i); rw [hc]; exact hκ
    filter_upwards [hB.receipt, ((Cards.largeMesh F).eventually_ge_atTop i).filter_mono hr] with w hw hV; change i≤w.1 at hV; unfold Cards.register at *; simp only [comp_apply,zoom_local _ hi _ _ hV]; simpa only [comp_apply] using hw

end YM.OPE.Log
