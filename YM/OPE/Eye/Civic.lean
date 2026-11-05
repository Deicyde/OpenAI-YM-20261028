import YM.OPE.Eye.Cloud
import YM.OPE.Eye.Admire
/-!
# Pass to arbitrary configurations (raw, and exterior of any given match)
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE
open Function Set Filter Lattice RG Wilson Cells Extraction Word Spec
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius
variable {G:Gauge}{C:Family G}{F : Extraction.Order}{S:Table C.book} (U : Final C F S) (h : Org.Grill C F)
variable {I J L : Type}[Fintype I][Fintype J] {A A' : ℝ}
variable {X Y : I → E4} {Z Z' : J → E4} {φ : Filter L} {H:L→I→E4}{R:L→J→E4}
    {v:I→ C.book.Token}{w:J→ C.book.Token}

def Apart (A:ℝ)(x:I→ E4):Prop:= ∀ i j, i≠j→ A<‖x i-x j‖
def ApartFrom (A:ℝ)(x:I→E4)(y:J→E4):Prop:=∀ i j,A<‖x i-y j‖
lemma Apart.coin (h:Apart A X)(hx:0 ≤ A) : Injective X:= by intro i j H; by_contra hh; have hp:=(hx.trans_lt (h i j hh)); rw [H,sub_self,norm_zero] at hp; exact lt_irrefl _ hp
lemma Apart.diagonal {W:Type}[Subsingleton W](A:ℝ)(x:W→E4):Apart A x:=fun _ _ h=> (h (Subsingleton.elim ..)).elim
lemma ApartFrom.together (h:ApartFrom A X Z)(hx:0≤A)(hZ:Injective X)(hI:Injective Z): Injective (beside X Z):=by
    refine beside_distinct.mpr ⟨hZ,hI,fun i j he=>?_⟩; have hh:= hx.trans_lt (h i j); rw [he,sub_self,norm_zero] at hh; exact lt_irrefl _ hh
lemma apart_limit (h:Tendsto H φ (𝓝 X))(hp:Apart A X) : ∀ᶠ i in φ,Apart A (H i):= eventually_all.mpr fun i=> eventually_all.mpr fun j=>
    eventually_all.mpr fun hz=> (((tendsto_pi_nhds.mp h i).sub (tendsto_pi_nhds.mp h j)).norm).eventually (lt_mem_nhds (hp i j hz))
lemma cross_limit (h:Tendsto H φ (𝓝 X))(hv:Tendsto R φ (𝓝 Z))(hp: ApartFrom A X Z) : ∀ᶠ i in φ,ApartFrom A (H i) (R i):= eventually_all.mpr fun i=> eventually_all.mpr fun j=>
    (((tendsto_pi_nhds.mp h i).sub (tendsto_pi_nhds.mp hv j)).norm).eventually (lt_mem_nhds (hp i j))
variable {k k' b l f n q : ℕ} {B:I→ℝ}{D:J→ℝ}
-- Common ledger forms
structure Prepared (v:I→C.book.Token)(f: Extraction.Order) (k:ℕ)(g:I→ℝ):Prop where
   here (j): ∀ᶠ i:ℕ×ℕ in f.fuse,Cards.PaidAt C.S i.1 i.2 k (C.beta i.1 i.2) (g j) (C.O i.1 i.2 (d:=(v j).1) (v j).2 0)
lemma Prepared.cost (h:Prepared (C:=C) v F k B): 0 ≤ ∏ i,B i := Finset.prod_nonneg fun i _=> (h.here i).exists.choose_spec.cost

include h in
lemma civic (hh: Apart (2*C.S.a b) X)(hp: Apart (2*C.S.a l) Z)(hd: ApartFrom (2*C.S.a b) X Z) (he:Cards.Hall C.S b l q f n (Fintype.card I) (Fintype.card J))
    (hB: Prepared (C:=C) v F q B)(hD: Prepared (C:=C) w F n D): ‖viewing U (beside X Z) (beside v w)‖ ≤ (∏ i,B i)*∏ j,D j:=by
    classical
    let x i:= Cloud.unitGrid C.S i ∅ (beside X Z); let y i:= x i ∘ Sum.inl; let z i:= x i ∘ Sum.inr; have hr : Tendsto x atTop (𝓝 (beside X Z)):= Cloud.gridded ∅ _ _
    have hx i:x i=beside (y i) (z i):= funext fun a=>by cases a <;> rfl
    have hF(i): Screen (x i) := Cloud.screened _ _ (C.S.a_pos _) _ _
    have hY:Tendsto y atTop (𝓝 X):= tendsto_pi_nhds.mpr fun i=> tendsto_pi_nhds.mp hr (.inl i); have hZ:Tendsto z atTop (𝓝 Z):= tendsto_pi_nhds.mpr fun i=> tendsto_pi_nhds.mp hr (.inr i)
    have hA(i): 0≤ 2*C.S.a i:= mul_nonneg zero_le_two (C.S.a_pos i|>.le)
    have hz := hd.together (hA _) (hh.coin (hA _)) (hp.coin (hA _)); apply (glance_contract U (mul_nonneg hB.cost hD.cost)).mpr; intro v'
    rw [glance_sees _ v' _ _ hz]; refine le_of_tendsto (((smooth_observe (spectator U v') (spectate U v').smooth (beside v w) hz).tendsto.comp hr).norm) ?_
    filter_upwards [apart_limit hY hh,apart_limit hZ hp, cross_limit hY hZ hd,eventually_ge_atTop b] with i hy H hg hs
    change ‖observe _ (x i) _‖ ≤ _; rw [← glance_sees U v' _ _ (hF i|>.coin),hx i]; apply le_trans (glance_bound ..)
    have heq i:= hx i ▸ (hF i);
    let q':=Cloud.grid ∅ (C.S.a i) (beside X Z) (fun _ _=>0); exact admiring (C:=C) U h (x:=q' ∘ Sum.inl) (y:=q' ∘ Sum.inr) hs hy H hg (heq i) he hB.here hD.here

-- reindex grid points for exterior at finer levels than main.
section
variable {x:I→ Cover} {h' : k≤ k'}
local notation "T'" => C.S.gridPoint k
local notation "Γ" => C.S.gridPoint k'
def zoom (S:Schedule)(h:k≤k')(x: Cover): Cover:= Cells.span S h 0 • x
lemma zoom_grid (h:k ≤ k')(x : Cover) : Γ (zoom C.S h x)= T' x:=by
    ext i; simp only [Schedule.gridPoint,zoom,WithLp.ofLp_toLp,Pi.smul_apply,nsmul_eq_mul,Int.cast_mul, Int.cast_natCast]; rw [← mul_assoc]; congr 1; exact C.S.embeds_scale (C.S.toDepth h _)
lemma zoom_local (x:Cover)(h:k≤ k')(N p:ℕ)(hN:k' ≤ N): location C.S k' N p (zoom C.S h x)=location C.S k N p x:=by
    unfold location zoom; rw [dif_pos hN,dif_pos (h.trans hN),Ratio.embed_wrap,Ratio.embed_wrap,smul_smul]; exact congr_arg (fun a:ℕ=>wrap _ (a • x)) (Work.B15.count_trans (C.S.toDepth hN p) (C.S.toDepth h p) (C.S.toDepth (h.trans hN) p)).symm
local notation "z0"=> (fun _ : Unit=> (0:E4))
variable {t:ℕ}{P: ℕ×ℕ→ C.label t}{a:C.label t} {𝓕: Filter (ℕ×ℕ)}
-- Estimate imported from torus
structure Remains (v:I→ C.book.Token) (𝓕: Filter (ℕ×ℕ)) (k f d : ℕ)(x : I→ Cover)(q:ℕ×ℕ→ C.label d)(A:ℝ) : Prop where
    receipt : ∀ᶠ i:ℕ×ℕ in 𝓕, Cards.PaidAt C.S i.1 i.2 f (C.beta i.1 i.2) A (Cards.register C k x (germ (frozen C v)) i.1 i.2 - C.O i.1 i.2 (q i) 0)
include h in
lemma viewing_admits (hk:b ≤ k)(hh: Screen (T' ∘ x))(hp: Apart (2*C.S.a l) Z)(hd:ApartFrom (2*C.S.a b) z0 Z) (hT:Injective (beside ((T') ∘ x) Z))
    (he:Cards.Hall C.S b l q f n 1 (Fintype.card J)) [𝓕.NeBot] (hr:𝓕 ≤ F.fuse)(hz:Tendsto P 𝓕 (𝓝 a))
    (hB: Remains (C:=C) v 𝓕 k q t x P A)(hD: Prepared (C:=C) w F n D) :
    ‖viewing U (beside (T' ∘ x) Z) (beside v w) - viewing U (beside z0 Z) (beside (fun _ : Unit=>⟨t,a⟩) w)‖ ≤ A * ∏ i,D i:=by
    classical
    let W:= insert (0:E4) (Finset.univ.image fun i=> (T') (x i)); let z i:= Cloud.unitGrid C.S i W Z; let y(i:ℕ):= Cloud.grid W (C.S.a i) Z (fun _ _=>0); let V (_ : Unit):C.book.Token:= ⟨t,a⟩
    have hZ:Tendsto z atTop (𝓝 Z):= Cloud.gridded W _ _; have hS(i): Screen (z i):= Cloud.screened _ _ (C.S.a_pos _) _ _
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
    refine mirrorMatch U h A (x:=zoom C.S hi ∘ x) (y:=y i) (hk.trans hi) hψ ?_ (hK.symm ▸ hG) (hc.symm ▸ hQ) he hr hz ?_ hD.here
    · change ApartFrom _ ((C.S.gridPoint i) ∘ _) (z i); rw [hc]; exact hκ
    filter_upwards [hB.receipt, ((Cards.largeMesh F).eventually_ge_atTop i).filter_mono hr] with w hw hV; change i≤w.1 at hV; unfold Cards.register at *; simp only [comp_apply,zoom_local _ hi _ _ hV]; simpa only [comp_apply] using hw
end
end YM.OPE
