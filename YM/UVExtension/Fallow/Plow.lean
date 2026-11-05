import YM.UVExtension.Fallow.Acre

/-! Forward primitive lattice differences, all bounded families\orders as paid.
At this stage literally on the torus/covers, eventually as the lattice
mesh vanishes. Orbit commands and tessellated positions in descendants. -/
set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Fallow
open Finset Filter Function MeasureTheory Set Lattice Wilson RG Cells Extraction Push GridApprox Hearth Metric
open Lease Dash Bid MergeProof RelayDifference Opening Local Next.Foundations Source
open scoped Topology BigOperators ContDiff Classical Matrix.Norms.Frobenius
variable {G:Gauge}{C:Family G}(hG:G.Simple)(H:Vintage.YM.Family.Makes C)(B:Stock.Tabs C.path.levels){W:Bid.Worth}{u ψ φ δ:ℕ→ℝ}{ζ:ℕ→ℕ→ℝ}{r:ℕ→ℕ}{D:∀ N p m:ℕ,m<N→MergeProof.GaugeDoor (C.path.rep N p (m+1)) (C.path.rep N p m)}
    (h:Scrim C W u ψ φ δ ζ r D) {d N n p:ℕ}
open Next.Extract Harvest
-- step on the literal torus.One higher real.Word bounds all mixed.
abbrev Axel (n:ℕ):= Fin n × Axis
abbrev Tabletop n:= Fin n→ Lattice.Cover

def hike {n :ℕ} (X: Axel n) : Tabletop n:= Work.D03.jump X.1 X.2

def climbing (t:ℝ)(w:Tabletop n→ℂ)(X:Axel n) (v:Tabletop n):ℂ:= (t:ℂ)⁻¹*(w (v+hike X)-w v)
-- order from tail to head
def rake (t:ℝ)(F:Tabletop n→ℂ): List (Axel n) → Tabletop n → ℂ
   | []=> F
   | x::xs=> climbing t (rake t F xs) x

def worked (F:Fin n → Stem C p)(s:Axel n): Fin n→ Stem C p:= update F s.1 (Fallow.entry (F s.1) s.2)
section torus
lemma stations (F:Fin n→ Stem C p) (hn:∀ i,Envelope (F i N)) (X:Axel n): Fallow.patch (worked F X) N = climbing (C.S.a N) (Fallow.patch F N) X:=by
    obtain ⟨i,a⟩:=X; funext v; let X:= wrap (C.side N p) ∘ v; let Y:= X i; let U':=wrap (C.side N p) ∘ (v+hike (i,a)); let g := worked F (i,a); let c:= C.beta N p
    let Z(j:Fin n)(x:Site (C.side N p)):= bloom (F j N) x; let S U:=∏ j∈Finset.univ.erase i,Z j (X j) U; let f (w:Site (C.side N p)):= moment c (fun u=>Z i w u*S u)
    have hw : U' i=X i+Lattice.step a:=by dsimp only [U',hike,Function.comp_apply]; simp [Work.D03.jump,X]
    have hv(j)(hh:j≠i): U' j=X j:=by unfold U' X hike; simp [Function.comp_apply, Work.D03.jump, hh]
    have h (W: Tabletop n)(Y:Fin n→ Stem C p)(hx:∀ j,j≠i→ wrap _ (W j)=X j)(hY:∀ j,j≠i →Y j= F j): Fallow.patch Y N W= moment c (fun u=>bloom (Y i N) (wrap _ (W i)) u*S u):=by
       unfold Fallow.patch garden; apply congr_arg; funext u; rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]; refine congr_arg (bloom _ _ u*·) (Finset.prod_congr rfl (fun j hj=> ?_)); dsimp only [Function.comp_apply]; rw [hx j (ne_of_mem_erase hj),hY j (ne_of_mem_erase hj)] -- z defeq
    rw [climbing,h v g (fun j _=>rfl) (fun j hj=>Function.update_of_ne hj ..), h _ _ hv (fun _ _=>rfl),h _ _ (fun j _=>rfl) (fun j _=>rfl)]; unfold g; simp only [worked,update_self]; rw [show wrap (C.side N p) ((v+hike (i,a)) i)=_ from hw,pushed]
    have he(j x): Envelope (Z j x):=(hn j).comp_env (law_translate 0 _).measurable
    have hS:Envelope S:=Envelope.prodC _ _ (fun j _=>he j _)
    have hz(w): Integrable (fun u=> Z i w u*S u) (law G _ c):=((he _ _).mulC hS).integrableC _
    unfold moment; rw [← integral_sub (hz _) (hz _), ← integral_const_mul]; refine integral_congr_ae ?_; filter_upwards with u; simp only [Pi.smul_apply, smul_eq_mul, Pi.sub_apply]; change ((C.S.a N:ℂ)⁻¹ * (Z i (X i+Lattice.step a) u-Z i (X i) u))*S u=(C.S.a N:ℂ)⁻¹*(Z i (X i+Lattice.step a) u*S u-Z i (X i) u*S u); ring
lemma moving (A:Stem C p) (h:Continuous (A N))(a:Axis) : Continuous (Fallow.entry A a N):=by
   unfold entry; refine Continuous.const_smul ((Continuous.sub (g:=A N) ?_ h)) _
   have hv : (Lattice.translate (K:=G.El) (Lattice.step a (S:=Per (C.side N p))))=Lattice.pull 1 (Lattice.step a):=funext fun U=> (pull_one _ U|>.symm)
   unfold bloom; rw [hv]; exact h.comp (continuous_pull ..)
lemma ledger (v:Fin n→ C.book.Token)(p:ℕ): Extraction.lifted C N p v= Fallow.patch (fun i=> plant (v i) p) N:=by
   funext L; unfold lifted Fallow.patch garden; rw [Family.num]; unfold moment; apply integral_congr_ae; filter_upwards with i; refine Finset.prod_congr rfl fun j _=>?_ ; rw [plant,blossoms]; rfl
end torus
variable (K:Extraction.Wcmain C)
include H K h hG B
section sail
variable (p:ℕ)(hs:Harvest.Harrow C u ζ)
include hs
lemma wagon (m:List (Axel n))(f:Fin n→ Stem C p)(d:Fin n→ℕ)(he:∀ i, garment (f i) (d i))(hp:∀ i,Wealth C (f i))(hC : ∀ i N, Continuous (f i N))(ht:∀ i,∀ k:ℕ,d i ≤ k→k ≤ d i + m.length→Slicing C k p) : ∃ g:Fin n→ Stem C p, ∃ a:Fin n→ℕ, (∀ i, Wealth C (g i)∧ garment (g i) (a i) ∧ (∀ N,Continuous (g i N))∧d i ≤ a i∧a i ≤ d i +m.length)∧∀ N,Fallow.patch g N=rake (C.S.a N) (Fallow.patch f N) m:=by
   induction m with
   | nil=> exact ⟨f,d,fun i=> ⟨hp _,he _,hC _,le_rfl,le_rfl⟩,fun N=> rfl⟩
   | cons i m ih=>
     obtain ⟨g,d',hG',hr⟩:= ih fun i k h he=> ht _ _ h (he.trans (by simp)); rcases i with ⟨i,a⟩
     have hh:= tending (hG' i|>.1.1) a; have hv(N):Continuous (Fallow.entry (g i) a N):= moving _ (hG' i|>.2.2.1 N) _; have hm:= cloakNext (g i) (hG' i|>.2.1) (hs.lab.shifts Extraction.Order.full) a
     have hd:d i ≤ d' i ∧ d' i+1 ≤ d i+(List.length ((i,a)::m)):= ⟨(hG' i).2.2.2.1,(Nat.add_le_add_right (hG' i|>.2.2.2.2) 1).trans_eq (Nat.add_assoc ..)⟩
     have hQ:= vetted hG H B h K (ht i _ (hd.1.trans (Nat.le_succ _)) hd.2) hs (Fallow.entry (g i) a) hh (Eventually.of_forall hv) hm (fun I hI=> spend H K I hI _ a (hG' i|>.1))
     refine ⟨worked g (i,a), update d' i (d' i+1),fun j=> ?_,fun N=> (stations g (fun i=> Envelope.compactC (hG' i|>.2.2.1 N)) (N:=N) _).trans ?_⟩
     · by_cases hp:j=i; · subst j; simp only [worked,update_self]; exact ⟨hQ,hm,hv,hd.1.trans (Nat.le_succ _),hd.2⟩
       simp only [worked,update_of_ne hp]; obtain ⟨hv,hH,ht,ha,hb⟩:=hG' j; exact ⟨hv,hH,ht,ha,hb.trans (by simp)⟩
     rw [hr]; rfl
-- scope hull before K. usable all lattice specs Nat.step organized later.
lemma reaped (m:List (Axel n))(v:Fin n→ C.book.Token)(Z:Set (Points n))(hr:IsCompact Z)(hz:Z⊆ NoHit C.S p n)(ht:∀ i,∀ k:ℕ,(v i).1≤ k→k≤(v i).1 + m.length→ Slicing C k p): ∃ b:ℝ,0 ≤ b∧ ∀ᶠ N in atTop,∀ o:Tabletop n, Extraction.tag (C.S.a N) o∈Z → ‖rake (C.S.a N) (lifted C N p v) m o‖ ≤ b:=by
   let V i := plant (v i) p; let x (i:Fin n): ℕ→ C.label ((v i).1):= fun _=> (v i).2; have he(i):Spar (x i):= Spar.rating _
   obtain ⟨g,d,hL,hP⟩:= wagon hG H B h K p hs m V (fun i=>(v i).1) (fun i=> cloak hG H (x i) _ (Bleak.physical H p (he i))) (fun i=>(thorC H K p (he i)).wealth) (fun i N=> C.continuousO N p ..) ht
   obtain ⟨b,hb,hF⟩:= cover H g Z hr hz (fun i=> (hL i).1)
   exact ⟨b,hb,hF.mono fun N hn o ht=> by rw [ledger v p,← show Fallow.patch g N=_ from hP N]; exact hn _ ht ⟩
end sail
end YM.UVExtension.Fallow
