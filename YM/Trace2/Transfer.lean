import YM.OPE.Single
import YM.Trace.Revel
import YM.EveryPhase.Extension

/-! Joint witness and comparison between character phases at trace scales. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 80000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Trace
open Function Set Filter Table Pairing Spec OPE
open scoped Topology BigOperators Matrix.Norms.Frobenius ContDiff
variable {G : Gauge} {C : Family G} {S : Table C.book} {f : Extraction.Order}

/-- Retain the sampled UV frames on the very same theory that supports the all-phase OPE estimates. -/
theorem echo_with_services (h : G.Simple) (b : ℝ) (hb : 0<b) (f : Extraction.Order) :
    ∃ C : Family G, C.Makes ∧ Calibrated C ∧ C.path.levels.clock.kernel.penalty=b ∧
     Extraction.Wcmain C ∧ ∃ (g : Extraction.Order) (T : Table C.book),
     Services C (f.refine g) T ∧ Nonempty (Echo C (f.refine g) T) := by
  obtain ⟨C,hB,hC,hM,hW,hS,H,hQ,hF⟩ := YM.PhysicalNext.Repeat.Legato.noel_columns h hb
  obtain ⟨g,A,L,R,T,E,hA,s,-⟩ := hF f
  obtain ⟨hs,hG⟩ := hQ (f.refine g) s.copies
  have hh : OPE.Services C (f.refine g) T:= ⟨hs,h,hS,A,L,R,E,hA⟩
  exact ⟨C,hM,hC,hB,hW,g,T,hh,
     graduated_echo (W:=E) H h hC hs hG s hA.clean.ready hA.clean.tilt⟩

variable (Y : Final C f S)
lemma every_same : ∃ L' : EveryPhase.Almanac Y, EveryPhase.Completed Y L' := EveryPhase.all_characters Y

include Y in
lemma first_grade (hG : G.Simple) {d : ℕ} (hd : d<4) (z : S.Field d) : ∃ t : ℂ,z=t • S.unit d := by
  obtain ⟨H,hH⟩ := Y.phase.transport.comparator
  obtain ⟨e, -, -⟩:=hH d
  have hr : Module.finrank ℂ (S.Field d)=1:= e.finrank_eq.trans (UVNext.FreeStress.dim_before _ hG hd)
  obtain ⟨t, ht⟩ := (finrank_eq_one_iff_of_nonzero' (S.unit d) (S.alive d Y.room.kernel.laws)).1 hr z
  exact ⟨t, ht.symm⟩

section Empty
variable {I : Type}[Fintype I] {J : Type}[Fintype J] [IsEmpty J]
lemma observe_beside_empty {B:Register G} {T:Table B} (h:T.Symmetric)
    (x:I→E4) (hx : Injective x) (p:I→B.Token) (y : J→E4)(q : J→B.Token) :
    observe T (beside x y) (beside p q) = observe T x p := by
  let e : I⊕J ≃ I :=
    { toFun:=fun s=>s.elim id isEmptyElim
      invFun:=Sum.inl
      left_inv:=by rintro (i|j); rfl; exact isEmptyElim j
      right_inv:=fun _=>rfl }
  have hx' : x ∘ e=beside x y:=by
    funext i; rcases i with i|j
    · rfl
    · exact isEmptyElim j
  have hp' : p ∘ e=beside p q:=by
    funext i; rcases i with i|j
    · rfl
    · exact isEmptyElim j
  rw [← hx',← hp',perm_observe T h e p hx]
end Empty

def oneToken {L : Register G} (T : Table L) (z : E4) (d : ℕ) (p : L.Ref d) : ℂ :=
    observe T (sole z) (fun _ : Unit => ⟨d,p⟩)
lemma singleton_read {L : Register G}(T : Table L)(h : T.Symmetric) (z : E4)(d : ℕ)(p : L.Ref d) :
    oneToken T z d p=T.read (points (fun _:Fin 1=>z)) (fun _=>⟨d,p⟩) := by
  let x:=points (fun _:Fin 1=>z)
  have hx : x∈ conf 1:=valid_one x
  let v:=fun (_:Fin 1) =>(⟨d,p⟩ : L.Token)
  rw [← named_fin T h v hx]; exact perm_observe T h (Equiv.ofUnique Unit (Fin 1)) v hx
  -- #check names
lemma oneToken_class {L : Register G} {S T : Table L}(h : T.Symmetric) (hr : T.respects S) (z : E4)(d : ℕ)(p : L.Ref d) :
    oneToken T z d p = S.classMoment T (n:=1) (fun _=> d) (points (fun _=>z)) (fun _=>S.project d p) :=
  (singleton_read T h z d p).trans (S.class_agrees T h hr (fun _:Fin 1=>d) (valid_one _) (fun _=>p)).symm
lemma oneToken_linear {L : Register G} (S T : Table L) (z : E4)(d:ℕ)(b:S.Field d) :
    S.classMoment T (fun _:Fin 1=>d) (points (fun _=>z)) (fun _=>b) =
       (S.classMoment T (fun _:Fin 1=>d) (points (fun _:Fin 1=>z))).toLinearMap (fun _=>0) 0 b := by
    rw [MultilinearMap.toLinearMap_apply]; congr 1; funext i; fin_cases i; simp
lemma oneToken_scalar {L : Register G} (S T : Table L)(h : T.Basic)(hr : T.respects S)(z : E4) (d : ℕ)
   (b : L.Ref d) (t : ℂ)(ht : S.project d b=t • S.unit d) : oneToken T z d b=t := by
   let x:=points (fun _:Fin 1=>z)
   let M : S.Field d →ₗ[ℂ] ℂ := (S.classMoment T (n:=1) (fun _=>d) x).toLinearMap (fun _=>0) 0
   have hM v : S.classMoment T (fun _:Fin 1=>d) x (fun _=>v)=M v:=by
     dsimp only [M];rw [MultilinearMap.toLinearMap_apply]; congr 1; funext i; fin_cases i; simp
   have he : M (S.unit d) = 1:=by
     rw [← hM]; change S.classMoment T (fun _=>d) x (fun _=> S.project d (L.scalar d))=1
     rw [S.class_agrees T h.toSymmetric hr _ (valid_one x) (fun _=>_)]
     change T.read x (fun _:Fin 1=>⟨d,L.scalar d⟩)=1
     rw [show (fun _:Fin 1=>⟨d,L.scalar d⟩:Fin (0+1)→L.Token)=Fin.cons (L.one d) (fun i : Fin 0=>L.one d) from funext (Fin.cases rfl (fun i=>Fin.elim0 i)),h.unital (valid_one ..)]
     exact h.trivial ..
   rw [oneToken_class h.toSymmetric hr,ht]
   rw [hM, map_smul,he,smul_eq_mul,mul_one]

variable {I : Type}[Fintype I] {J : Type}[Fintype J] {m : ℕ} (P : Prescription Y.sector.derivatives)
open OPE.Prescription
open scoped Classical
lemma vacuum_truncation [IsEmpty J] (hG : G.Simple) (r : Viewers Y) (x : I→E4) (p : I→ C.book.Token) (o : E4) (y : J→E4) (q : J→ C.book.Token) :
    P.truncated (spectator Y r) 0 x p o y q=P.truncated S 0 x p o y q := by
  let T:=spectator Y r
  have ht : T.Hierarchy:=spectate Y r
  have hr : T.respects S:=spectate_respects Y r
  have hh:=ht.laws
  have hs:=Y.room.kernel.laws
  refine Finset.sum_congr rfl fun t h=>?_ 
  obtain ⟨⟨⟩, b⟩:=t
  · unfold termRead
    change _ * observe T _ _ = _
    rw [observe_beside_empty hh.toSymmetric (sole o) (Function.injective_of_subsingleton (sole o)), observe_beside_empty hs.toSymmetric (sole o) (Function.injective_of_subsingleton (sole o))]
    apply congr_arg
    let v:= (P.letter ⟨0,b⟩).snd
    change oneToken T o 0 v=oneToken S o 0 v
    obtain ⟨b,hb⟩:= first_grade Y hG (by omega : 0<4) (S.project 0 v)
    exact (oneToken_scalar S T hh hr o 0 v b hb).trans (oneToken_scalar S S hs (fun _=>le_rfl) o 0 v b hb).symm
  simp [full_bands] at h
lemma vacuum_error (H : SingleSubpower Y P)(hG:G.Simple)(p:I→C.book.Token) {x:ℝ→ I→ E4}{o:ℝ→E4}(M η ε:ℝ) (hM : 0≤ M) (hη:0<η) (hε : 0<ε) :
   ∀ᶠ r:ℝ in 𝓝[>]0, WithinRoom r M η (x r) (o r) → ∀ v w:Viewers Y,
       ‖observe (spectator Y v) (x r) p-observe (spectator Y w) (x r) p‖ ≤ 2*r^(1-(sigma p:ℝ)-ε) := by
   let y:Empty→E4 := Empty.elim
   let q:Empty→C.book.Token := Empty.elim
   filter_upwards [H.horizons I Empty p q η M 1 ε hη hM one_pos hε 0] with r hr h
   let A:=r^(1-(sigma p:ℝ)-ε)
   have he (a : Viewers Y) : ‖observe (spectator Y a) (x r) p-P.truncated S 0 (x r) p (o r) y q‖ ≤ A:= by
      rw [← vacuum_truncation Y P hG a]
      obtain ⟨hK,-,hR⟩:=hr (x r) (o r) y h ⟨fun i=> Empty.elim i,fun i=> Empty.elim i⟩
      rw [← observe_beside_empty (spectate Y a).laws.toSymmetric (x r) (beside_distinct.mp hK).1 p y q]
      simpa only [Nat.cast_zero,zero_add] using hR.phaseBound a
   intro v w; let K:=P.truncated S 0 (x r) p (o r) y q
   refine (norm_sub_le_norm_sub_add_norm_sub _ K _).trans ?_
   calc ‖observe (spectator Y v) (x r) p-K‖ + ‖K-observe (spectator Y w) (x r) p‖ = ‖observe (spectator Y v) (x r) p-K‖ + ‖observe (spectator Y w) (x r) p-K‖ := congrArg _ (norm_sub_rev _ _)
        _ ≤ _ := (add_le_add (he v) (he w)).trans_eq (two_mul A).symm

/-- Unit subtraction physically chosen on each character (and on unselected law). -/
def massCenter (i:Viewers Y) : ℝ := ((S.classMoment (spectator Y i) (fun _:Fin 1=>4) 0) (fun _=>theta Y 0)).re
lemma massCenter_eq (i:Viewers Y) : ((massCenter Y i):ℂ)=(S.classMoment (spectator Y i) (fun _:Fin 1=>4) 0) (fun _=>theta Y 0) := by
    let K:=spectator Y i; have hK:=spectate Y i; have hr:=spectate_respects Y i
    let v:=oneToken K 0 4 (S.representative 4 (theta Y 0))
    have he : v= S.classMoment K (fun _:Fin 1=>4) 0 (fun _=>theta Y 0) := (oneToken_class hK.laws.toSymmetric hr ..).trans (congr_arg _ (funext (fun _=>S.rep ..)))
    have hv : star v=v:=by
      rw [he]; obtain ⟨a,ha⟩:=S.onto _ (theta Y 0)
      have hh:=(hK.spin.real (x:=0) (valid_one _) (fun _:Fin 1=>⟨4,a⟩))
      change K.value (n:=1) (fun _=>4) 0 (fun _=>star a)= _ at hh
      have ht : S.project 4 (star a)=theta Y 0:= by rw [← theta_real Y 0, ← ha,S.conj_project]
      calc
         _ = star (K.value (fun _:Fin 1=>4) 0 (fun _=>a)) := by simp_rw [← ha, S.class_agrees K hK.laws.toSymmetric hr _ (valid_one 0)]
         _ = K.value (fun _:Fin 1=>4) 0 (fun _=>star a) := hh.symm
         _ = _ := by rw [← S.class_agrees K hK.laws.toSymmetric hr _ (valid_one 0)]; simp_rw [ht]

    have hR := congrArg Complex.im hv
    apply Complex.ext; · rfl
    rw [Complex.star_def,Complex.conj_im] at hR
    rw [Complex.ofReal_im]
    rw [← show K=spectator Y i from rfl, ← he]; linarith only [hR]
lemma trace_mean_at (i:Viewers Y) (z:E4) : oneToken (spectator Y i) z _ (S.representative 4 (theta Y 0)) = (massCenter Y i : ℂ) := by
  let T:=spectator Y i; have ht:=spectate Y i; have h:=ht.laws.toSymmetric
  have h1 (t:E4) (a:C.book.Ref 4) : oneToken T t 4 a =oneToken T 0 4 a :=(singleton_read T h ..).trans (Eq.trans ?_ (singleton_read T h ..).symm)
  case refine_1=>
    exact Eq.trans (congr_arg (T.read · _) (PiLp.ext (fun _=>by change _ = 0+t; simp))) (ht.translations 1 (points (fun _=>0)) (valid_one _) t _)
  change oneToken T z _ _=_
  rw [h1,massCenter_eq,oneToken_class h (spectate_respects Y i)]
  simp_rw [S.rep]; rfl
local notation "stamp" => ![(0:Fin 2),1]
lemma trace_eval_right (i:Viewers Y){x : Points 2}(hx : x∈ conf 2){x' : S.Field 4}{a:ℂ}
    (ha : ∀ (p:C.book.Ref 4), S.project 4 p=x' → ∀ z: E4, oneToken (spectator Y i) z 4 p=a) :
    S.classMoment (spectator Y i) (n:=2) (fun _=>4) x ![S.unit 4,x']=a := by
    let B:=spectator Y i;have hB:=(spectate Y i).laws;have hr:=spectate_respects Y i
    obtain ⟨q,rfl⟩:=S.onto _ x'
    have hb : (fun j:Fin 2=>⟨4,![C.book.scalar 4,q] j⟩:Fin 2→C.book.Token)=Fin.cons (C.book.one 4) (fun (_:Fin 1)=>⟨4,q⟩):=by
       funext j; fin_cases j <;> rfl
    rw [show (![S.unit 4,S.project _ q])=(fun j=>S.project 4 (![C.book.scalar 4,q] j)) from funext (by intro j; fin_cases j <;> rfl),S.class_agrees B hB.toSymmetric hr _ hx]
    change B.read x (fun j=> ⟨4,![C.book.scalar 4,q] j⟩) = _ ; rw [hb, hB.unital (by convert hx)]
    exact Eq.trans (congr_arg (B.read · _) (PiLp.ext (fun j:Fin 1=>by fin_cases j; rfl) : x.tail = points (fun (_:Fin 1)=> x 1)))  ((singleton_read B hB.toSymmetric ..).symm.trans <| ha q rfl _)
lemma eval_exchange {L:Register G} (T B:Table L)(hB : B.Symmetric) (p q : T.Field 4)(x:Points 2)(hx:x∈ conf 2): let k:=Equiv.swap 0 1; let M z:=T.classMoment B (fun _ : Fin 2 =>4) z
    M x ![p,q]= M (Points.rearrange k x) ![q,p] := by
  intro k M
  let r:(Fin 2)→L.Token:= fun j=>⟨4,T.representative _ (![p,q] j)⟩
  change B.read x r = B.read _ (fun j=> ⟨4,T.representative _ (![q,p] j)⟩)
  have ht : (fun j => (⟨4,T.representative _ (![q,p] j)⟩ : L.Token))=r ∘ k:=by
      funext i; fin_cases i <;> simp [r,k]
  rw [ht,hB.same k hx r]

def cape := (‖viewing Y (sole 0) (fun (_:Unit)=> ⟨4, S.representative 4 (theta Y 0)⟩)‖)
lemma cape_bounds (i:Viewers Y) : ‖massCenter Y i‖ ≤ cape Y := by
  rw [← Complex.norm_real]
  rw [← trace_mean_at Y i 0]
  unfold oneToken; rw [← glance_sees Y i _ _ (Function.injective_of_subsingleton (sole (0:E4)))]; exact glance_bound .. 

def traceEta (i:Viewers Y) (x:Points 2) (e t:ℂ) : ℂ:= S.classMoment (spectator Y i) (fun _:Fin 2 =>4) x ![theta Y 0 - e • S.unit _,theta Y 0- t • S.unit _]
lemma centered_formula (i:Viewers Y){x:Points 2} (hx:x∈conf 2)(e t:ℂ): traceEta Y i x e t = traceEta Y i x 0 0 - (e+t)*(massCenter Y i)+e*t:= by
   let T:=theta Y 0; let q:=S.unit 4; let B:=spectator Y i; have hB:=spectate Y i;have hs:=hB.laws.toSymmetric
   let m:ℂ:=massCenter Y i
   have hT (b) (hb:S.project 4 b=T) (z:E4): oneToken B z 4 b=m:= Eq.trans (Eq.trans (by exact oneToken_class hs (spectate_respects Y i) ..) ?_) (trace_mean_at Y i z)
   case refine_1=> simp_rw [hb,oneToken_class (S:=S) hs (spectate_respects Y i) z 4 (S.representative _ _), S.rep];rfl
   let M {z: Points 2} := S.classMoment B (fun _:Fin 2=>4) z
   let K (p r:S.Field 4):= M (z:=x) ![p,r]
   let hl v : (S.Field 4) →ₗ[ℂ] ℂ:= M (z:=x).toLinearMap ![q,v] 0
   have hp {z:Points 2}(hz:z∈conf 2): M (z:=z) ![q,T]=m:= trace_eval_right Y i hz hT
   have hq : K T q=m:= (eval_exchange S B hs _ _ x hx).trans (hp (Points.rearrange_in _ hx))
   have ht : K q q=1:= trace_eval_right Y i hx fun p hp z=> by simpa only [one_smul] using oneToken_scalar S B hB.laws (spectate_respects Y i) z 4 p 1 (hp.trans (one_smul ℂ q).symm)
   change K _ _ = K _ _- _+ e*t
   have h1 p v : hl v p=K p v:= by simp_rw [hl,MultilinearMap.toLinearMap_apply]; congr 1; funext i; fin_cases i <;> simp
   let hr v:= (M (z:=x)).toLinearMap ![v,q] 1
   have h2 r v : hr v r=K v r:= by simp_rw [hr,MultilinearMap.toLinearMap_apply]; congr 1; funext i; fin_cases i <;> simp
   simp only [← h1, map_sub, map_smul, smul_eq_mul]
   simp only [h1, ← h2, map_sub, map_smul, smul_eq_mul]
   simp only [h2]
   simp [← show T = theta Y 0 from rfl, ← show q = S.unit 4 from rfl, ← show m = (massCenter Y i : ℂ) from rfl,hq,ht,show K q T=m from hp hx];ring


def uncenter (Y : Final C f S) (i : Viewers Y) (x:Points 2) : ℂ:=observe (spectator Y i) x.ofLp (fun _ : Fin 2=>⟨4,S.representative 4 (theta Y 0)⟩)
def central (Y : Final C f S) (i : Viewers Y) (x:Points 2) : ℂ:=traceEta Y i x (massCenter Y i) (massCenter Y i)
lemma uncenter_eq (i : Viewers Y) {x:Points 2}(hx:x∈conf _): uncenter Y i x=traceEta Y i x 0 0:= by
    unfold traceEta uncenter; rw [named_fin _ (spectate Y i).laws.toSymmetric _ hx]
    simp only [zero_smul,sub_zero]; change _= (S.classMoment _ _ x) ![_,_]
    rw [show ![theta Y 0,theta Y 0]=(fun _=>theta Y 0) from funext (by intro i; fin_cases i <;>rfl)]
    rfl
lemma personality (i : Viewers Y) {x : Points 2}(hx:x∈conf _): ‖central Y i x-uncenter Y i x‖ ≤ (cape Y)^2:= by
    let m:=massCenter Y i
    rw [central, centered_formula Y i hx, uncenter_eq Y i hx,sub_add_eq_add_sub, sub_right_comm,add_sub_cancel_left]
    change ‖(↑m:ℂ)*(m)- ((m:ℂ)+(m:ℂ))*m‖ ≤ _
    rw [show (m:ℂ)*↑m- _ = - (m:ℂ)^2 from by ring,norm_neg,norm_pow,Complex.norm_real]
    exact pow_le_pow_left₀ (norm_nonneg _) (cape_bounds ..) _
lemma room_conf (x : Points 2)(o:E4)(r M η :ℝ)(h : WithinRoom r M η x.ofLp o)(hr:0<r)(hη:0<η): x∈ conf _ := by
    intro i j he; by_contra hj; exact ne_of_gt ((mul_pos hη hr).trans_le (h.spaced i j hj)) (by simp [he])

/-- Error comparing the exact trace pair at any two character phases
(or to the unselected hierarchy): subpower R^{-1+ε} in engineering units on compact separated shapes. -/
theorem centered_phased (H : Services C f S) {M ε η:ℝ} (hM:0≤M)(hε:0<ε)(hη:0<η):
    ∀ᶠ r:ℝ in 𝓝[>]0, ∀ (x : Points 2) (o:E4), WithinRoom r M η x.ofLp o → ∀ v w:Viewers Y,
       ‖central Y v x - central Y w x‖ ≤ 2*(cape Y)^2 +2*r^(-7-ε) := by
    obtain ⟨p,hp₀⟩:= OPE.Prescription.chosen Y.room.kernel.laws.toSymmetric Y.phase.transport.injection
    have hp:= OPE.one_radius Y (P:=p) hp₀ H
    let b:=fun _:Fin 2=> (⟨4,S.representative 4 (theta Y 0)⟩ : C.book.Token)
    suffices hl : ∀ x:ℝ→ Points 2,∀ o:ℝ→E4, ∀ᶠ r:ℝ in 𝓝[>]0, WithinRoom r M η (x r).ofLp (o r) → ∀ (v w:Viewers Y),‖central Y v (x r) - central Y w (x r)‖ ≤ 2*(cape Y)^2+2*r^(-7-ε) by
       have h:= universalize (V:=Points 2×E4) (φ:=𝓝[>]0) (p:=fun r:ℝ=> fun (x,o)=> WithinRoom r M η x.ofLp o → ∀ v w:Viewers Y,‖central Y v x-central Y w x‖ ≤ 2*(cape Y)^2+2*r^(-7-ε)) (fun t=>hl (fun i=>(t i).1) (fun i=>(t i).2))
       exact h.mono (fun i hi x t=>hi (x,t))
    intro x o; filter_upwards [self_mem_nhdsWithin (s:=Ioi (0:ℝ)) (a:=0), vacuum_error Y p hp H.simpleGate b (x:=fun i=>(x i).ofLp) (o:=o) M η ε hM hη hε] with r hr he hh v w
    have hl:=room_conf _ _ _ _ _ hh hr hη
    let K:= fun u=> central Y u (x r); let U:=fun a=>uncenter Y a (x r)
    have h1 : ‖U v-U w‖ ≤ 2*r^(-7-ε) :=by
        apply (he hh v w).trans_eq; congr 2
        norm_num [sigma, b, Fin.sum_univ_two]
    have h2 (i:Viewers Y) := personality Y i hl
    exact (norm_sub_le_norm_sub_add_norm_sub (K v) (U v) _).trans (((add_le_add (h2 _) (norm_sub_le_norm_sub_add_norm_sub (U v) (U w) _)).trans (add_le_add (le_refl _) (add_le_add h1 ((norm_sub_rev _ _).trans_le (h2 w))))).trans_eq (by ring))
local notation "wgt" r:max => r^(8:ℕ)*Real.log (r⁻¹)^2
lemma log_weight_rate (a : ℝ): Tendsto (fun r:ℝ=> |wgt r| *(2*a+2*r^(-7.5 : ℝ))) (𝓝[>]0) (𝓝 0) := by
   have hm:= ((tendsto_log_mul_rpow_nhdsGT_zero (r:=8/2) (by norm_num)).pow 2).mul_const (2*a)
   have ht:= ((tendsto_log_mul_rpow_nhdsGT_zero (r:=0.5/2) (by norm_num)).pow 2).mul_const 2
   rw [zero_pow (by omega : 2≠0),zero_mul] at ht hm
   have hH :=hm.add ht; rw [zero_add] at hH; apply hH.congr' ((show ∀ᶠ x:ℝ in 𝓝[>] 0,x>0 from self_mem_nhdsWithin).mono fun x hx=> ?_)
   · rw [abs_of_nonneg (by positivity),Real.log_inv]
     have he {a b c:ℝ} (hc : c=a*2+b) : x^c=(x^a)^ (2:ℕ)*x^b:=by rw [hc,Real.rpow_add hx,Real.rpow_mul hx.le,Real.rpow_two]
     have h7:=he (show (0.5/2)*2 = (4:ℝ)*2+(-7.5) by norm_num);rw [Real.rpow_mul hx.le,Real.rpow_two] at h7
     have h8:x^(8:ℕ)=(x^(4:ℝ))^(2:ℕ):=by norm_num; ring
     rw [mul_pow,mul_pow,h8,h7]; norm_num; ring_nf
   -- fix
/-- Full-scale quantitative universality of any candidate logarithmic limit. -/
def LogAgreement (Y:Final C f S): Prop:= ∀ (M η:ℝ) (δ:ℝ), 0<δ→0≤M→0<η→
   ∀ᶠ r:ℝ in 𝓝[>]0,∀ x: Points 2, ∀ o, WithinRoom r M η x.ofLp o→∀ i j:Viewers Y,
      ‖(wgt r:ℝ) • (central Y i x-central Y j x)‖ < δ
lemma log_agreement (H:Services C f S): LogAgreement Y := by
   intro M η δ hδ hM hη
   filter_upwards [centered_phased Y H (M:=M) (ε:=0.5) (η:=η) hM (by norm_num) hη,
      (log_weight_rate ((cape Y)^2)).eventually (gt_mem_nhds hδ)] with r hr h x o hx i j
   rw [norm_smul,Real.norm_eq_abs]; rw [show (-7.5:ℝ) = -7-0.5 by norm_num] at h; exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left (hr x o hx i j) (abs_nonneg _)) h

end YM.Trace
