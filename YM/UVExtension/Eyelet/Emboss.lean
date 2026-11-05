import YM.UVExtension.Eyelet.Stella
/-! angular observer on rack labels AFTER reorientation. transform analytically in parameter later -/
set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Eyelet
open Function Filter MeasureTheory Set Lattice Wilson RG Source Extra.Histories Labels
open Planned.GuardedAtom Guard Push Local MergeProof Next.Foundations Concert BoundedContinuousFunction
open Motion
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical
variable {G:Gauge}{n:Side}{d :ℕ}{F:Frame G d}{H: Hol G}{p: BudgetPoint}{R:Rep G n} {ι:Type}(m:Motion)

def stripe (n:Side): StockTag n≃StockTag n:= Equiv.subtypeEquiv (puff m 0) (by
    intro i; let f:=sky m (0:Site n); change _ ↔ (f i.2).Nonempty ∧ f i.2⊆ f i.1; unfold f; simp only [shading, Finset.image_nonempty]; rw [Finset.image_subset_image_iff (turnSites m.1 (0:Site n)).injective])
lemma shire (i:StockTag n): (stripe m n i).val=puff m 0 i.val:=rfl
lemma cruises {f:Config G n→ℂ}(i:StockTag n)(hf:Tail p i f) : Tail p (stripe m n i) (dance m f):=by
   obtain ⟨b,hB⟩:=hf.earns; let T:=stripe m n i; have he:T.val.1=sky m 0 i.val.1:=rfl; have hv : T.val.1= i.val.1.image (turnSites m.1 0):=shading ..
   have hk: Measurable (Motion.scalar m):=by unfold Motion.scalar; split_ifs; exact continuous_star.measurable; exact measurable_id
   refine ⟨fun U V hX ht=> congr_arg (Motion.scalar m) (uses_pull hf.read m.1 0 U V (hv ▸ hX) (hv ▸ ht)), hk.comp (hf.bop.comp (continuous_pull ..).measurable),fun g U=>congr_arg (Motion.scalar m) (invariant_pull hf.shelf m.1 0 g U),?_,?_,b,fun U=>(norm_scalar m _).le.trans (hB _)⟩
   · intro h; change 0∈ T.val.1; rw [hv]; have ht := Finset.mem_image_of_mem (turnSites m.1 (0:Site n)) (hf.posed (fun hz=> h (by rw [hz]; exact funext fun i=> scalar_z m))); rw [nought m] at ht; exact ht
   intro U hz; have hp:= hf.poll (pull m.1 0 U) (fun h=>hz (by unfold dance; rw [h,scalar_z])); let x:Site n:=0; change sky m x _ ∩ _= sky m x _
   nth_rw 1 [← Work.H03.flags_send m.1 x p.threshold U]; simp_rw [shading]; rw [show affine m.1 x=⇑(turnSites m.1 x) from rfl,← Finset.image_inter _ _ (turnSites m.1 x).injective]; exact congr_arg _ hp
variable (H p d)
def crane (i:StockTag n) : Bolt (G:=G) p i →ₛₗ[gazeH m] Bolt (G:=G) p (stripe m n i) where
    toFun x:=⟨dance m x.val,cruises m i x.property⟩
    map_add' f g:=Subtype.ext (funext fun j=> Motion.scalar_add m _ _)
    map_smul' c f:=Subtype.ext (funext fun j=>by rw [tintA]; exact Motion.scalar_mul m _ _)

lemma soldK (i:StockTag n) : ∃ (T:Stream G p i→SL[gazeH m] Stream G p (stripe m n i)), (∀ x,T (twig _ x)=twig _ (crane (G:=G) p m i x))∧ ∀ v,‖T v‖≤ ‖v‖ :=by
    let A:=crane (G:=G) p m i; let T:Bolt p i→ₛₗ[gazeH m] Stream G p _:= (twig (sink (G:=G) p _)).comp A; let L:=twig (sink (G:=G) p i)
    have h(x:Bolt (G:=G) p i):‖T x‖ ≤ 1*‖L x‖:= by
       rw [one_mul]; exact (debts p _ (A x)).1 (fun U=> (norm_scalar m _).trans_le ((sink _ _ x).norm_coe_le_norm ⟨_⟩))
    exact ⟨T.extendOfNorm L,fun x=> LinearMap.extendOfNorm_eq (steams _) ⟨_,h⟩ x,fun v=> (LinearMap.norm_extendOfNorm_apply_le (steams _) _ h v).trans (one_mul ..|>.le)⟩
variable {p H d} (S:R.activities.Moves m.1 (0:Site n))(Q:Coefficient F n) {η:ℝ} (h:Eligible Q H R η)(Z: Eligible (audition S Q) H R η)
-- price witness contains BOTH.
local notation "T'"=> Equiv.prodCongr (shift m n) (Equiv.refl ℕ)
lemma dyes (hn:2≤ n.val) (i: Eyelet.Slot n): Z.fernP (T' i)= capt d H R.p m hn i.1 (h.fernP i):=by
   let j:= T' i; apply Subtype.ext; change graft (audition S Q) j=dance m (graft Q i)
   have hv : (audition S Q).support j.2= (Q.support i.2).image (turnSites m.1 0):=by unfold audition; split <;> rfl
   have he : j.1.val=i.1.val.image (turnSites m.1 0):=shading ..
   unfold graft; rw [hv,he]; simp only [(Finset.image_injective (turnSites m.1 0).injective).eq_iff]; split
   next h => unfold audition dance Motion.scalar; split <;> rfl
   next h => exact funext fun _=> (scalar_z m).symm

lemma rungE (H:Hol G)(p:BudgetPoint)(hn:2≤ n.val) : let M:= fun i:Eyelet.Slot n=> (soldE d H p m hn i.1).choose
    ∃ T:Roc d H n p →SL[gazeH m] Roc d H n p, (∀ v i,T v (Equiv.prodCongr (shift m n) (Equiv.refl ℕ) i)=M i (v i))∧ ∀ v,‖T v‖ ≤ Local.turnCost p.order p.power*‖v‖:=by -- M i with target defeq?
    intro M
    let T (i:Eyelet.Slot n) : Gondola d H i.1 p→SL[gazeH m] Gondola d H ((T' i).1) p:=M i
    have hx:= blouse (E:=fun i:Eyelet.Slot n=> Gondola d H i.1 p) (T:=fun i:Eyelet.Slot n=>Gondola d H i.1 p) m (T') T (pow_nonneg (by positivity) _) (fun i=> (soldE d H p m hn i.1).choose_spec.2)
    exact hx
lemma rungK (G:Gauge) (p:BudgetPoint) (n:Side): let M:= fun i:StockTag n=> (soldK (G:=G) p m i).choose
    ∃ T:Coil G n p →SL[gazeH m] Coil G n p, (∀ v i,T v (stripe m n i)=M i (v i))∧ ∀ v,‖T v‖≤1*‖v‖:=
    blouse (E:=fun i:StockTag n=> Stream G p i) (T:=fun i:StockTag n=> Stream G p i) m (stripe m n) _ zero_le_one (fun i x=> ((soldK (G:=G) p m i).choose_spec.2 x).trans_eq (one_mul ..).symm)

def spinsE (H:Hol G)(p:BudgetPoint)(hn:2≤ n.val): Roc d H n p→SL[gazeH m] Roc d H n p:= (rungE m H p hn).choose

def spinsK (n:Side)(p:BudgetPoint): Coil G n p→SL[gazeH m] Coil G n p:= (rungK m G p n).choose
lemma sprint (hn:2≤ n.val): spinsE (d:=d) m H R.p hn h.tollE=Z.tollE:=by
    refine lp.ext (funext (fun j=>?_))
    obtain ⟨i,rfl⟩:= (T').surjective j; let L:= tin d H i.1 R.p
    let u:= (T' i).1.val
    have he:u = i.1.val.image (turnSites m.1 0):=shading ..
    have hp : fee R.p u= fee R.p i.1.val:=by unfold fee; rw [he,cover_map _ (turn_sep m.1 0)]
    unfold spinsE; rw [show _=_ from ((rungE (d:=d) m H R.p hn).choose_spec.1 h.tollE i)] -- goal cast?
    let g:=(soldE d H R.p m hn i.1).choose; let v:= fee R.p i.1.val
    change g ((v:ℂ) • twig _ (h.fernP i))=(↑(fee R.p u):ℂ) • twig _ _; rw [map_smulₛₗ g,tintA,scalar_real,show g (twig (tin d H i.1 R.p) _) =_ from (soldE d H R.p m hn i.1).choose_spec.1 (h.fernP i), hp,dyes m S Q h Z hn i]; rfl
lemma leaps : spinsK m n R.p h.tollK= Z.tollK:=by
    refine lp.ext (funext fun i=>?_); obtain ⟨i,rfl⟩:= (stripe m n).surjective i
    let T:=stripe m n i
    have hp:T.val=puff m 0 i.val:=rfl
    have he: Z.sapP T= crane R.p m i (h.sapP i):=by
      apply Subtype.ext; change profile R.activities _ T.val=dance m (profile R.activities Q.forced i.val); rw [foyer,hp]; unfold floatUp; rw [Equiv.symm_apply_apply]; rfl
    let K:= (soldK (G:=G) R.p m i).choose
    have hx : fee R.p T.val.1=fee R.p i.val.1:=by unfold fee; rw [show T.val.1=i.val.1.image (turnSites m.1 0) from shading .., cover_map _ (turn_sep m.1 0)]
    unfold spinsK; rw [show _=_ from ((rungK m G R.p n).choose_spec.1 h.tollK i)]
    change K (((fee R.p i.val.1/η:ℝ):ℂ) • twig _ (h.sapP i))=((fee R.p T.val.1/η:ℝ):ℂ) • twig _ (Z.sapP T); rw [he,hx,map_smulₛₗ K,tintA,scalar_real,show K (twig (sink (G:=G) R.p i) (h.sapP i))= _ from (soldK (G:=G) R.p m i).choose_spec.1 (h.sapP i)]
end YM.UVExtension.Eyelet
