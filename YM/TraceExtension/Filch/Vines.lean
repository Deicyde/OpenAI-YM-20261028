import YM.TraceExtension.Filch.Lion
import YM.TraceExtension.Filch.Manor
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Filch
open Function Filter Matrix Lattice Precision Laurent Stationary Perfect Exterior Tree RG Wilson Finset Push.Uniform Det Planned.PrimaryIntegral295 Drupes
open scoped BigOperators Topology ContDiff Matrix.Norms.Frobenius Classical
variable {G:Gauge}

lemma crop_ext(G:Gauge)(C:ℝ)(k:ℕ)(h:0≤ C): ∃ f:ℕ→ℝ, MarksP f ∧ ∀ (X:Type)[NormedAddCommGroup X] [NormedSpace ℝ X] {n:Side}(U:X→ Config G n)(v:X→ Link G n)(x:X), (∀ i,Allows k (fun y=> G.mat (U y i)) x C) → (∀ e:Edge (Site n), Allows k (fun y=> edgeColor (v y) e) x C) → ∀ o r j,landW o j ≤ r→ Allows k (fun y=> patio o 4 (U y) (v y) j) x (f r):=by
    obtain ⟨D,hD,H⟩:= prophet G 4 k
    obtain ⟨L,hL,hA⟩:= shaders G k
    let T:(i:ℕ)→ℝ:=fun i=> travelCost G k (4*i) C
    let V(i):=composeCost k D (swarm G k i C); let E:= (ContinuousLinearMap.apply ℝ G.Color (E:=G.Color)).flip
    let Z(i):= composeCost k L (T i); let F(i):= V i + 2^k * ‖E‖ * Z i * C
    let J (j:G.ColorIndex):= EuclideanSpace.proj j (𝕜:=ℝ); let N:ℝ:=∑ i, ‖J i‖
    have hJ(j):‖J j‖ ≤ N:= Finset.single_le_sum (fun i _=>norm_nonneg (J i)) (mem_univ j); have hN:0≤ N:=sum_nonneg fun i _=>norm_nonneg (J i)
    have hv := (token D hD).composeM k (market G C h k); have hz := (token L (by positivity)).composeM k
         (MarksP.travelM G k (fun i=>4*i) C h (by simpa using covG 0))
    have ht:= ((token (2^k * ‖E‖) (by positivity)).pair hz).pair (token C h)
    refine ⟨_, (token N hN).pair ((hv.booth ht):MarksP F),?_⟩; intro X _ _ n U v x hu hp o r j he
    cases j with
    | inl j=>
        rcases j with ⟨y,b,l⟩; obtain ⟨b,rfl⟩:= axisEquiv.surjective b
        let A z:= flock o (U z) (y,b); have ha:= H X A _ x (stepsH o U x k C hu y he b)
        have hh(z): patio o 4 (U z) (v z) (.inl (y,axisEquiv b,l)) = J l (nimbus G 4 (A z)):= patioX ..
        simp_rw[hh]; exact ((ha.mono (M:=F r) (le_add_of_nonneg_right (ht.1 _))).linear (J l) (hJ _))
    | inr j=>
        rcases j with ⟨y,b,l⟩; obtain ⟨b,rfl⟩:=axisEquiv.surjective b
        let A z:= march o (U z) y
        let Q z:= (G.adjoint (A z)).toContinuousLinearMap
        let P z:= edgeColor (v z) (y,b)
        have ha : Allows k Q x (Z r):=by unfold Q; simp_rw [Drupes.turned]; exact (hA _).comp (f:=fun z=>G.mat (A z)) (priced o U x k C hu y he)
        have hx:= ha.bilinear E (hp (y,b)) le_rfl
        have hh(z): patio o 4 (U z) (v z) (.inr (y,axisEquiv b,l)) = J l (E (Q z) (P z)):=patioY ..
        simp_rw [hh]; exact ((hx.mono (M:=F r) (le_add_of_nonneg_left (hv.1 _))).linear (J l) (hJ _))
end YM.Trace.Filch
noncomputable section
namespace YM.Trace.Filch
open Function Filter Matrix Lattice Precision Laurent Stationary Perfect Exterior Tree RG Wilson Finset Push.Uniform Det Planned.PrimaryIntegral295 Drupes
open scoped BigOperators Topology ContDiff Matrix.Norms.Frobenius Classical
variable {G:Gauge}{n:Side}{k:ℕ}{o:Site n}{r:ℕ}{F:Acr G n→ℝ}
lemma requestsP (j:pairA G n)(h:landW o j ≤ r): Requests Set.univ (fun x=> par o 4 x j) (af G n) o (4*(r+1+1)):=by
    intro v _ w _ H
    let t:=4*(r+1+1); let P:=feed o (r+1)
    let x:=aleft G n v; let y:=aleft G n w; let f:=aright G n v; let g:= aright G n w; let U:=input G n x; let V:=input G n y
    have he:Agrees P U V:=by
       intro e he _; obtain ⟨b,hb,he⟩:= halo_spec.mp (show e.1∈ P from he); rw [mem_singleton.mp hb] at he; unfold U V; rw [input_color,input_color]; apply congr_arg; ext i; exact H (.inl (e.1,coord e.2,i)) he
    cases j with
    | inl j=> rcases j with ⟨a,b,i⟩; obtain ⟨b,rfl⟩:= axisEquiv.surjective b; change patio o 4 U f (.inl (a,coord b,i))= patio o 4 V g (.inl (a,coord b,i)); rw [patioX,patioX]; exact congr_arg (fun x=> nimbus G 4 x i) (eaten _ _ _ (r:=r) h _ _ he)
    | inr j=>
       rcases j with ⟨a,b,i⟩; obtain ⟨b,rfl⟩:=axisEquiv.surjective b; change separation o a≤r at h; change patio o 4 U f (.inr (a,coord b,i))=patio o 4 V g (.inr (a,coord b,i)); rw [patioY,patioY,show march o U a= march o V a from grazes _ _ (r:=r+1) (by omega) _ _ he]
       rw [show edgeColor f (a,b)=edgeColor g (a,b) from ?_]; ext j; exact H (.inr (a,coord b,j)) (show separation o a ≤ _ from by omega)
lemma parPay(G:Gauge):∃ f:ℕ→ℝ, MarksP f ∧∀ (n:Side)(o:Site n)(r:ℕ)(j:pairA G n), landW o j ≤ r→ Allows 4 (fun x=>par o 4 x j) 0 (f r):=by
    obtain ⟨D,hD,H⟩:=Det.spike_m G 4
    let A:= ContinuousLinearMap.fst ℝ G.Color G.Color; let B:= ContinuousLinearMap.snd ℝ G.Color G.Color
    obtain ⟨E,hE,h⟩ := exists_allows (s:={(0:G.Color)}) (f:=G.mat ∘ G.lieExp) isCompact_singleton (fun x _=> G.exp_jet.contDiffAt) 4
    let M:= ‖A‖*D; let K:= ‖B‖*D; let Z:= composeCost 4 E M; have hk:0 ≤ K:=by positivity
    have hz:0 ≤ Z:=by unfold Z M composeCost; positivity
    obtain ⟨F,hF,Hf⟩:= crop_ext G (Z+K) 4 (add_nonneg hz hk)
    refine ⟨F,hF,fun n o r j he=>?_⟩
    let U(x:Acr G n):=input G n (aleft G n x); let P(e:Edge (Site n))(x:Acr G n):=(edgeColor (aleft G n x) e,edgeColor (aright G n x) e)
    have hu(e:Edge (Site n)) : Allows 4 (fun x=>G.mat (U x e)) 0 (Z+K):=by
        have hp:A (P e 0)=0:=by simp[A,P]
        have hx := (show Allows 4 (G.mat ∘ G.lieExp) (A (P e 0)) E from hp.symm ▸ h _ (Set.mem_singleton _)).comp (f:=fun x=>A (P e x)) ((H n e (P e) rfl).linear A le_rfl)
        exact (hx.mono (le_add_of_nonneg_right hk)).germ (Eventually.of_forall fun x=>(congr_arg G.mat (input_color (aleft G n x) e)).symm)
    exact Hf (Acr G n) U (aright G n) 0 hu (fun e=> ((H n e (P e) rfl).linear B le_rfl).mono (le_add_of_nonneg_left hz)) o r j he
end YM.Trace.Filch
